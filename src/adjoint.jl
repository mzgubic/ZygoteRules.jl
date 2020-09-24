using MacroTools
using MacroTools: @q, combinedef
using ChainRulesCore: AbstractZero, Zero, DoesNotExist, Composite

named(arg) = isexpr(arg, :(::)) && length(arg.args) == 1 ? :($(gensym())::$(arg.args[1])) : arg

typeless(x) = MacroTools.postwalk(x -> isexpr(x, :(::), :kw) ? x.args[1] : x, x)
isvararg(x) = isexpr(x, :(::)) && namify(x.args[2]) == :Vararg

"""
    generic2diff(x)

Convert input `x` from the legacy ZygoteRules format to the ChainRules differential types.
"""
generic2diff(x) = x
generic2diff(::Nothing) = Zero()
generic2diff(t::Union{Tuple, NamedTuple}) = map(generic2diff, t)

"""
    diff2generic(x)

Convert input `x` from the ChainRules differential types to the legacy ZygoteRules format.
"""
diff2generic(x) = x
diff2generic(::AbstractZero) = nothing
diff2generic(t::Union{Tuple, NamedTuple}) = map(diff2generic, t)
function diff2generic(::Nothing)
    @error "Zygote internal use  of 'nothing', rather than `AbstractZero`, detected.  This should never occur. Please open an issue on https://github.com/FluxML/Zygote.jl/issues, including the full text of this message"  stacktrace=stacktrace()
    return nothing
end

for n = 0:3
  gradtuple = Symbol(:gradtuple, n)
  @eval begin
    $gradtuple(x::Tuple) = ($(ntuple(_->:(DoesNotExist()),n)...), x...)
    $gradtuple(x::AbstractZero) = x
    $gradtuple(x) = error("Gradient $x should be a tuple")
  end
end

abstract type AContext end
function adjoint end
function _pullback end
function pullback end

say(x) = (println("say ", x); return x)

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
      y, _back = adjoint(__context__, $f, $(argnames...))
      $(mut ? nothing : :(back(::Union{Nothing,AbstractZero}) = Zero()))
      #back(Δ) = $gradtuple(generic2diff(_back(diff2generic(Δ))))
      back(Δ) = $gradtuple(say(generic2diff(say(_back(Δ)))))
      return y, back
    end
    @inline function ZygoteRules._pullback($cx, ::$kT, kw, $f::$T, $(args...)) where $(Ts...)
      y, _back = adjoint(__context__, $f, $(argnames...); kw...)
      $(mut ? nothing : :(back(::Union{Nothing,AbstractZero}) = Zero()))
      #back(Δ) = $gradtuplekw(generic2diff(_back(diff2generic(Δ))))
      back(Δ) = $gradtuplekw(say(generic2diff(say(_back(Δ)))))
      return y, back
    end
    nothing # why is this here?
  end
end

macro adjoint(ex)
  gradm(ex)
end

macro adjoint!(ex)
  gradm(ex, true)
end
