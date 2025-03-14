############ managing functions symbols ################

#### First, we make a basic tree system 

abstract type AbstractCodeSpace end
abstract type NSyntaxNode end

const NodeType = Union{Number, NSyntaxNode, Symbol}

struct NSyntaxTree{T <: NSyntaxNode}
    root::T
end
NSyntaxTree(n::NSyntaxNode) = NSyntaxTree{typeof(n)}(n)

mutable struct SymbolicSpace{T <: Any} <: AbstractCodeSpace 
    code::NSyntaxTree
    const var::Dict{Symbol, T}

    ## Constructor 

    SymbolicSpace{T}() where T<: Any = new{T}(NSyntaxTree(), Dict{Symbol, T}())
    SymbolicSpace{T}(ex::Expr) where T<: Any = new{T}(totree(ex), Dict{Symbol, T}())
    
end

struct ConstNode{T <: Number}
    n::T
end
ConstNode(n::NodeType) = ConstNode{typeof(n)}(n)

struct SymbNode
    n::Symbol
end

struct AddNode{T <: NSyntaxNode, N <: NSyntaxNode}
    n1::T
    n2::N
    AddNode{T, N}(n1::T, n2::N) where {T <: NSyntaxNode, N <: NSyntaxNode} = new(n1, n2)
end

function AddNode(n1::NSyntaxNode, n2::NSyntaxNode)
    if n1 isa ConstNode && n2 isa ConstNode
        return ConstNode(n1.n + n2.n)
    elseif iszero(n1)
        return n2
    elseif iszero(n2)
        return n1
    else
        return AddNode{typeof(n1), typeof(n2)}(n1, n2)
    end
end
AddNode(n1::NodeType, n2::NodeType) = AddNode(_make_node(n1), _make_node(n2))

struct SubNode{T <: NSyntaxNode, N <: NSyntaxNode}
    n1::T
    n2::N
    SubNode{T, N}(n1::T, n2::N) where {T <: NSyntaxNode, N <: NSyntaxNode} = new(n1, n2)
end

function SubNode(n1::NSyntaxNode, n2::NSyntaxNode)
    if n1 isa ConstNode && n2 isa ConstNode
        return ConstNode(n1.n - n2.n)
    elseif iszero(n2)
        return n1
    else
        return SubNode{typeof(n1), typeof(n2)}(n1, n2)
    end
end
SubNode(n1::NodeType, n2::NodeType) = SubNode(_make_node(n1), _make_node(n2))

struct ProdNode{T <: NSyntaxNode, N <: NSyntaxNode}
    n1::T
    n2::N
    ProdNode{T, N}(n1::T, n2::N) where {T <: NSyntaxNode, N <: NSyntaxNode} = new(n1, n2)
end

function ProdNode(n1::NSyntaxNode, n2::NSyntaxNode)
    if n1 isa ConstNode && n2 isa ConstNode
        return ConstNode(n1.n * n2.n)
    elseif iszero(n1) || iszero(n2)
        return ConstNode(0)
    elseif isone(n1)
        return n2
    elseif isone(n2)
        return n1
    else
        return ProdNode{typeof(n1), typeof(n2)}(n1, n2)
    end
end
ProdNode(n1::NodeType, n2::NodeType) = ProdNode(_make_node(n1), _make_node(n2))

struct PowNode{T <: NSyntaxNode, N <: NSyntaxNode}
    n1::T
    n2::N
    PowNode{T, N}(n1::T, n2::N) where {T <: NSyntaxNode, N <: NSyntaxNode} = new(n1, n2)
end

function PowNode(n1::NSyntaxNode, n2::NSyntaxNode)
    if n1 isa ConstNode && n2 isa ConstNode
        return ConstNode(n1.n ^ n2.n)
    elseif iszero(n1)
        return ConstNode(0)
    elseif iszero(n2)
        return ConstNode(1)
    else
        return PowNode{typeof(n1), typeof(n2)}(n1, n2)
    end
end
PowNode(n1::NodeType, n2::NodeType) = PowNode(_make_node(n1), _make_node(n2))

### Spaces function 

setvar(space::SymbolicSpace{T}, s::Symbol, val) = (space.var[s] = convert(T, init))

####### Operations 

Base.getindex(n::NSyntaxNode, I::Integer) = begin
    fields = fieldnames(typeof(n))
    getfield(n, fields[I])
end

iszero(n::NSyntaxNode) = false
iszero(n::ConstNode) = iszero(n.n)

isone(n::NSyntaxNode) = false
isone(n::ConstNode) = isone(n.n)

get_children(A::AbstractArray) = A
get_children(e::Expr) = e.args
get_children(n) = ()

is_leave(n) = isempty(get_children(n))

const SymType = Union{Symbol,Expr, Number}

negate(n::NSyntaxNode) = n

derivate(n::Number) = 0
derivate(n::ConstNode) = 0
derivate(n::SymbNode) = 1

derivate(n::AddNode) = AddNode(derivate(n.n1), derivate(n.n2))
derivate(n::SubNode) = SubNode(derivate(n.n1), derivate(n.n2))
derivate(n::ProdNode) = AddNode(ProdNode(derivate(n.n1), n.n2), ProdNode(n.n1, derivate(n.n2)))
derivate(n::PowNode) = ProdNode(ProdNode(n.n2, derivate(n.n1)), PowNode(n.n1, ConstNode(n.n2[1] - 1)))

derivate(::Val{:+}, f::SymType, g::SymType) = Expr(:call, :+, derivate(f), derivate(g))
derivate(::Val{:-}, f::SymType, g::SymType) = Expr(:call, :-, derivate(f), derivate(g))
derivate(::Val{:*}, f::SymType, g::SymType) = Expr(:call, :+, Expr(:call, :*, derivate(f), g), Expr(:call, :*, derivate(g), f))
derivate(::Val{:*}, f::SymType, n::Number) = derivate(Val(:*), n, f)
derivate(::Val{:*}, n::Number, f::SymType) = n == 0 ? 0 : (n == 1 ? derivate(f) : Expr(:call, :*, n, derivate(f)))
derivate(::Val{:^}, f::SymType, n::Number) = n == 1 ? derivate(f) : Expr(:call, :*, n, Expr(:call, :^, f, n - 1), derivate(f))

derivate(ex::Expr) = derivative(ex)
derivate(s::Symbol) = 1
derivate(tree::NSyntaxTree) = NSyntaxTree(derivate(tree.root))

getop(::AddNode) = :+
getop(::SubNode) = :-
getop(::ProdNode) = :*
getop(::PowNode) = :^

toexpr(n::ConstNode) = n.n
toexpr(n::SymbNode) = n.n
toexpr(n::NSyntaxNode) = Expr(:call, getop(n), toexpr(n.n1), toexpr(n.n2))

totree(ex::Expr) = NSyntaxTree(_make_node(ex))

_make_node(n::Number) = ConstNode(n)
_make_node(s::Symbol) = SymbNode(s)
_make_node(::Val{:+}, n1::NodeType, n2::NodeType) = AddNode(n1, n2)
_make_node(::Val{:-}, n1::NodeType, n2::NodeType) = SubNode(n1, n2)
_make_node(::Val{:*}, n1::NodeType, n2::NodeType) = ProdNode(n1, n2)
_make_node(::Val{:^}, n1::NodeType, n2::NodeType) = PowNode(n1, n2)
_make_node(ex::Expr) = begin
    ch = ex.args
    if length(ch) == 2
        _make_node(Val(ch[1]), ch[2])
    elseif length(ch) == 3
        _make_node(Val(ch[1]), ch[2], ch[3])
    end
end

function clean_derivative(ex::Expr)
    ch = ex.args
    cderivate(Val(ch[1]), ch[2], ch[3])
end

cderivate(::Val{:+}, f, g) = Expr(:call, :+, f, g)
cderivate(::Val{:+}, f, n::Number) = iszero(n) ? f : Expr(:call, :+, f, n)
cderivate(::Val{:+}, n::Number, f) = cderivate(Val(:+), f, n)
cderivate(::Val{:+}, n1::Number, n2::Number) = n1 + n2
cderivate(::Val{:-}, f, g) = Expr(:call, :-, f, g)
cderivate(::Val{:-}, f, n::Number) = iszero(n) ? f : Expr(:call, :-, f, n)
cderivate(::Val{:-}, n::Number, f) = Expr(:call, :-, f, n)
cderivate(::Val{:-}, n1::Number, n2::Number) = n1 - n2
cderivate(::Val{:*}, f, g) = Expr(:call, :*, f, g)
cderivate(::Val{:*}, f, n::Number) = iszero(n) ? 0 : Expr(:call, :*, n, f)
cderivate(::Val{:*}, n::Number, f) = cderivate(Val(:*), f, n)
cderivate(::Val{:*}, n1::Number, n2::Number) = n1 * n2
cderivate(::Val{:^}, f, n::Number) = iszero(n) ? 1 : (isone(n) ? f : Expr(:call, :^, f, n))
cderivate(::Val{:^}, n1::Number, n2::Number) = n1 ^ n2

function derivative(ex::Expr)
    ch = ex.args
    if !is_leave(ex)
        der = derivate(Val(ch[1]), ch[2], ch[3])
        return der
    end
    return :()
end

### Evaluate code

Base.eval(sp::SymbolicSpace) = eval(sp.code, sp.var)
Base.eval(tr::NSyntaxTree, var::Dict) = eval(tr.root, var)
Base.eval(n::AddNode, var::Dict) = eval(n[1], var) + eval(n[2], var)
Base.eval(n::SubNode, var::Dict) = eval(n[1], var) - eval(n[2], var)
Base.eval(n::ProdNode, var::Dict) = eval(n[1], var) * eval(n[2], var)
Base.eval(n::PowNode, var::Dict) = eval(n[1], var) ^ eval(n[2], var)
Base.eval(n::ConstNode, var::Dict) = n[1]
Base.eval(s::SymbNode, var::Dict) = var[s[1]]


substitute(n::Number, _) = n
substitute(s::Symbol, sub::Pair{Symbol,<:Number}) = s == sub.first ? sub.second : s
function substitute(ex::Expr, sub)
    Expr(ex.head, [substitute(arg, sub) for arg in ex.args]...)
end

eval_func(ex::Expr, v::Number) = substitute(ex, :x => v) |> eval

precompile(derivate, (Val{:+}, Expr, Number))
precompile(derivate, (Val{:+}, Number, Expr))
precompile(derivate, (Val{:+}, Expr, Expr))
precompile(derivate, (Val{:-}, Expr, Number))
precompile(derivate, (Val{:-}, Number, Expr))
precompile(derivate, (Val{:-}, Expr, Expr))
precompile(derivate, (Val{:*}, Expr, Number))
precompile(derivate, (Val{:*}, Number, Expr))
precompile(derivate, (Val{:*}, Expr, Expr))
precompile(derivate, (Val{:^}, Expr, Number))
precompile(derivate, (Val{:^}, Symbol, Number))
precompile(derivate, (Val{:^}, Expr, Expr))