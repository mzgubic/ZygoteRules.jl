using MacroTools
using MacroTools: @q, combinedef
using ChainRulesCore: AbstractZero, Zero, DoesNotExist, Composite, unthunk, canonicalize

named(arg) = isexpr(arg, :(::)) && length(arg.args) == 1 ? :($(gensym())::$(arg.args[1])) : arg

typeless(x) = MacroTools.postwalk(x -> isexpr(x, :(::), :kw) ? x.args[1] : x, x)
isvararg(x) = isexpr(x, :(::)) && namify(x.args[2]) == :Vararg

"""
    legacytype_warn()

Issue a warning that a ChainRules differential type was expected but a Zygote legacy type
was received. This is used to report bugs in transitioning to ChainRules types and can be
deleted once/if `@adjoint` macro is deprecated.
"""
function legacytype_warn(::Type{T}) where T
  # can't use logging macros as that breaks nested AD.
  Core.println("""
    Zygote internal use of $T, rather than AbstractZero/Composite,
    detected. This should never occur. Please open an issue on
    https://github.com/FluxML/Zygote.jl/issues, including the full text of this message.
    Stacktrace:"""
  )
  for (i, callsite) in enumerate(stacktrace())
    Core.println("[$i] $callsite")
  end
end

"""
    difftype_warn()

Issue a warning that a Zygote legacy type was expected but a ChainRules differential type
was received. This is used to report bugs in transitioning to ChainRules types and can be
deleted once/if `@adjoint` macro is deprecated.
"""
function difftype_warn(x)
  # can't use logging macros as that breaks nested AD.
  Core.println("""
    $x passed when Nothing/Tuple/NamedTuple expected. This should never
    occur. Please open an issue on https://github.com/FluxML/Zygote.jl/issues, including
    the full text of this message.
    Stacktrace:"""
  )
  for (i, callsite) in enumerate(stacktrace())
    Core.println("[$i] $callsite")
  end
end

"""
    legacy2differential(x)

Convert input `x` from the legacy ZygoteRules format to the ChainRules differential types.
"""
legacy2differential(x, ::Any) = x
legacy2differential(::Nothing, ::Any) = Zero()
legacy2differential(t::Tuple, primal_types::Tuple) = map(l2d, t, primal_types)
legacy2differential(t::Tuple, primal_types) = (@warn "primal_types should be a tuple, not $primal_types"; return t)

l2d(x, ::Any) = x
l2d(::Nothing, ::Any) = Zero()
l2d(a::AbstractArray{<:Number}, primal_type) = a
l2d(a::AbstractArray, primal_type) = l2d.(a, eltype(primal_type))
l2d(a::AbstractArray, primal_type::AbstractArray{T}) where T = l2d.(a, primal_type) # TODO: T or primal_type?
l2d(x::Union{AbstractZero, Composite}, ::Any) = (difftype_warn(x); return x)
function l2d(t::Tuple, primal_type)
  primal_field_types = fieldtypes(primal_type)
  tp = map(l2d, t, primal_field_types)
  return canonicalize(Composite{primal_type, typeof(tp)}(tp))
end

function l2d(t::NamedTuple, primal_type)
  if !isabstracttype(primal_type)
    primal_field_types = NamedTuple{Tuple(fieldnames(primal_type))}(fieldtypes(primal_type))
    tp = map(l2d, t, primal_field_types)
    return canonicalize(Composite{primal_type, typeof(tp)}(tp))
  else
    #TODO: we could fix this if we had the primal values
    @warn "Could not determine Primal Type. This may make bad composites. This is caused by `Array{Any}` containing structs and similar."
    tp = l2d.(t, Any)
    return canonicalize(Composite{primal_type, typeof(tp)}(tp))
  end
end

"""
    differential2legacy(x)

Convert input `x` from the ChainRules differential types to the legacy ZygoteRules format.
"""
differential2legacy(x) = unthunk(x) # TODO eventually remove this
differential2legacy(::AbstractZero) = nothing
differential2legacy(t::Union{Tuple, NamedTuple}) = map(differential2legacy, t)
differential2legacy(::Nothing) = (legacytype_warn(Nothing); return nothing)
#differential2legacy(x::Tuple{Vararg{AbstractZero}}) = Zero() # TODO should this happen?
differential2legacy(a::AbstractArray) = differential2legacy.(a) # TODO: what to do with arrays with nothing?
differential2legacy(a::AbstractArray{<:Number}) = a
for T_outer in (:Tuple, :NamedTuple)
  # we create separate methods rather than using a `Union` + an `if` so that we avoid a
  # branch that changes output type, because nested AD on that kinda thing makes Zygote less
  # than happy.
  @eval @inline function differential2legacy(x::Composite{P, T}) where {P, T<:$T_outer}
    xp = map(differential2legacy, canonicalize(x))
    convert($T_outer, xp)
  end
end

for n = 0:3
  gradtuple = Symbol(:gradtuple, n)
  @eval begin
    $gradtuple(x::Tuple) = ($(ntuple(_->:(nothing),n)...), x...)
    $gradtuple(x::AbstractZero) = (difftype_warn(x); nothing) # TODO for now, remove these later once the warnings are fixed
    $gradtuple(::Nothing) = nothing
    $gradtuple(x) = error("Gradient $x should be a tuple")
  end
end

diffgradtuple1(x::Tuple) = (DoesNotExist(), x...)
diffgradtuple1(x::AbstractZero) = x
diffgradtuple1(::Nothing) = (legacytype_warn(x); DoesNotExist())
diffgradtuple1(x) = error("Gradient $x should be a tuple")

abstract type AContext end
function adjoint end
function _pullback end
function pullback end

function gradm(ex, mut = false)
  @capture(shortdef(ex), (name_(args__) = body_) |
                         (name_(args__) where {Ts__} = body_)) || error("Need a function definition")
  kw = length(args) > 1 && isexpr(args[1], :parameters) ? esc(popfirst!(args)) : nothing
  isclosure = isexpr(name, :(::)) && length(name.args) > 1
  f, T = isexpr(name, :(::)) ?
    (length(name.args) == 1 ? (esc(gensym()), esc(name.args[1])) : esc.(name.args)) :
    (esc(gensym()), :(Core.Typeof($(esc(name)))))
  kT = :(Core.kwftype($T))
  Ts == nothing && (Ts = [])
  args = named.(args)
  argnames = Any[typeless(arg) for arg in args]
  !isempty(args) && isvararg(args[end]) && (argnames[end] = :($(argnames[end])...,))
  args = esc.(args)
  argnames = esc.(argnames)
  Ts = esc.(Ts)
  cx = :($(esc(:__context__))::AContext)
  fargs = kw == nothing ? [cx, :($f::$T), args...] : [kw, cx, :($f::$T), args...]
  gradtuple   = isclosure ? gradtuple0 : gradtuple1
  gradtuplekw = isclosure ? gradtuple2 : gradtuple3
  adj = @q @inline ZygoteRules.adjoint($(fargs...)) where $(Ts...) = $(esc(body))
  quote
    $adj
    @inline function ZygoteRules._pullback($cx, $f::$T, $(args...)) where $(Ts...)
      argtypes = map(typeof, ($(argnames...),))
      y, _back = adjoint(__context__, $f, $(argnames...))
      $(mut ? nothing : :(back(::Union{Nothing,AbstractZero}) = Zero()))
      function back(Δ)
        _partials = _back(differential2legacy(Δ))
        if _partials isa Tuple && any(x isa Union{AbstractZero, Composite} for x in _partials)
          println("Wrong partial type returned. adjoint definition:")
          @show ($(QuoteNode(ex)))
        end
        if _partials isa Union{AbstractZero, Composite}
          println("Wrong partial type returned. adjoint definition:")
          @show ($(QuoteNode(ex)))
        end

        try
          legacy2differential($gradtuple(_partials), ($T, argtypes...))
        catch
          println("Error occured. adjoint definition:")
          @show ($(QuoteNode(ex)))
          rethrow()
        end
      end
      return y, back
    end
    @inline function ZygoteRules._pullback($cx, ::$kT, kw, $f::$T, $(args...)) where $(Ts...)
      argtypes = map(typeof, ($(argnames...),))
      y, _back = adjoint(__context__, $f, $(argnames...); kw...)
      $(mut ? nothing : :(back(::Union{Nothing,AbstractZero}) = Zero()))
      #back(Δ) = $gradtuplekw(legacy2differential(_partials, argtypes))
      function back(Δ)
        _partials = _back(differential2legacy(Δ))
        legacy2differential($gradtuplekw(_partials), ($kT, typeof(kw), $T, argtypes...))
      end
      return y, back
    end
    return nothing  # make nothing show in terminal after using macro
  end
end

macro adjoint(ex)
  gradm(ex)
end

macro adjoint!(ex)
  gradm(ex, true)
end
