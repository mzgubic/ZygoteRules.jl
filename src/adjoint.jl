using MacroTools
using MacroTools: @q, combinedef
using ChainRulesCore: AbstractZero, Zero, DoesNotExist, Composite, unthunk

named(arg) = isexpr(arg, :(::)) && length(arg.args) == 1 ? :($(gensym())::$(arg.args[1])) : arg

typeless(x) = MacroTools.postwalk(x -> isexpr(x, :(::), :kw) ? x.args[1] : x, x)
isvararg(x) = isexpr(x, :(::)) && namify(x.args[2]) == :Vararg

"""
    generic2diff(x)

Convert input `x` from the legacy Zygote format to the ChainRules differential types.
Zygote used to use tuples to represent both a collection of gradients w.r.t. a number of
arguments but also to represent the gradient of a tuple. This means that the gradients
w.r.t a tuple and a scalar would be represented as ((gt1, gt2, gt3), gs). The wrapper
function `generic2diff` takes care of the collection, while a gradient w.r.t. to a tuple
is taken care of by g2d to be represented as a ChainRules.Composite type.
"""
generic2diff(x) = error("Gradient $x should be a tuple")
generic2diff(::Nothing) = Zero()
generic2diff(x::Union{AbstractZero, Composite}) = x # TODO: remove this once complete (shouldnt happen?)
generic2diff(t::Tuple) = map(g2d, t)

g2d(x) = x
g2d(::Nothing) = Zero()
function g2d(t::Union{Tuple, NamedTuple})
  tp = map(g2d, t)
  Composite{Any, typeof(tp)}(tp)
end

"""
    diff2generic(x)

Convert input `x` from the ChainRules differential types to the legacy ZygoteRules format.
"""
diff2generic(x) = unthunk(x)
diff2generic(::AbstractZero) = nothing
diff2generic(t::Union{Tuple, NamedTuple}) = map(diff2generic, t)
function diff2generic(::Nothing)
    @error "Zygote internal use  of 'nothing', rather than `AbstractZero`, detected.  This should never occur. Please open an issue on https://github.com/FluxML/Zygote.jl/issues, including the full text of this message"  stacktrace=stacktrace()
    return nothing
end
#diff2generic(x::Tuple{Vararg{AbstractZero}}) = Zero() # TODO should this happen?
diff2generic(t::Union{Tuple, NamedTuple}) = map(diff2generic, t)
for T_outer in (:Tuple, :NamedTuple)
  # we create separate methods rather than using a `Union` + an `if` so that we avoid a
  # branch that changes output type, because nested AD on that kinda thing makes Zygote less
  # than happy.
  @eval @inline function diff2generic(x::Composite{P, T}) where {P, T<:$T_outer}
    xp = map(diff2generic, x)
    convert($T_outer, xp)
  end
end

for n = 0:3
  gradtuple = Symbol(:gradtuple, n)
  @eval begin
    $gradtuple(x::Tuple) = ($(ntuple(_->:(DoesNotExist()),n)...), x...)
    $gradtuple(x::AbstractZero) = x
    $gradtuple(x::Composite) = x
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
