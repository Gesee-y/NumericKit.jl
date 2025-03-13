############ managing functions symbols ################

#### First, we make a basic tree system 

abstract type NSyntaxNode

const NodeType = Union{Number, NSyntaxNode, Symbol}

struct NSyntaxTree{T <: NSyntaxNode}
    root::T
end

NSyntaxTree(n::NSyntaxNode) = NSyntaxTree{typeof(n)}(n)

struct ConstNode{T <: Number}
    n::T
end
ConstNode(n::NodeType) = ConstNode{typeof(n)}(n)

struct SymbNode
    n::Symbol
end

struct AddNode{T <: NodeType, N <: NodeType}
    n1::T
    n2::N

    ## Constructor

    function AddNode{T, N}(n1::T, n2::N where{T <: NodeType, N <: NodeType}
        if n1 isa ConstNode && n2 isa ConstNode
            v = n1[1] + n2[2]
            return ConstNode{type of(v)}(v)
        end
        
        iszero(n1) && return n2
        iszero(n2) && return n1

        return new{T, N}(n1, n2)
    end
end
AddNode(n1::NodeType, n2::NodeType) = AddNode{typeof(n1), typeof(n2)}(n1,n2)

struct SubNode{T <: NodeType, N <: NodeType}
    n1::T
    n2::N

    ## Constructor

    function SubNode{T, N}(n1::T, n2::N where{T <: NodeType, N <: NodeType}
        if n1 isa ConstNode && n2 isa ConstNode
            v = n1[1] - n2[2]
            return ConstNode{type of(v)}(v)
        end

        iszero(n1) && return negate(n2)
        iszero(n2) && return n1

        return new{T, N}(n1, n2)
    end
end
SubNode(n1::NodeType, n2::NodeType) = SubNode{typeof(n1), typeof(n2)}(n1,n2)

struct ProdNode{T <: NodeType, N <: NodeType}
    n1::T
    n2::N

    ## Constructor

    function ProdNode{T, N}(n1::T, n2::N where{T <: NodeType, N <: NodeType}
        if n1 isa ConstNode && n2 isa ConstNode
            v = n1[1] * n2[2]
            return ConstNode{type of(v)}(v)
        end

        (iszero(n1) || iszero(n2)) && return ConstNode{Int}(0)

        return new{T, N}(n1, n2)
    end
end
ProdNode(n1::NodeType, n2::NodeType) = ProdNode{typeof(n1), typeof(n2)}(n1,n2)

struct PowNode{T <: NodeType, N <: NodeType}
    n1::T
    n2::N

    ## Constructor

    function PowNode{T, N}(n1::T, n2::N where{T <: NodeType, N <: NodeType}
        if n1 isa ConstNode && n2 isa ConstNode
            v = n1[1] ^ n2[2]
            return ConstNode{type of(v)}(v)
        end

        iszero(n1) && return ConstNode{Int}(0)
        iszero(n2) && return ConstNode{Int}(1)

        return new{T, N}(n1, n2)
    end
end
PowNode(n1::NodeType, n2::NodeType) = PowNode{typeof(n1), typeof(n2)}(n1,n2)

####### Operations 

get_children(A::AbstractArray) = A
get_children(e::Expr) = e.args
get_children(n) = ()

is_leave(n) = isempty(get_children(n))

const SymType = Union{Symbol,Expr, Number}
### Managing Symbols

negate(n::NSyntaxNode) = n

derivate(n::Number) = 0
derivate(n::ConstNode) = 0

## Addition rule
derivate(::Val{:+}, f::SymType, g::SymType,) = Expr(:call, :+, derivate(f), derivate(g))
derivate(n::AddNode) = AddNode(derivate(n[1]), derivate(n[2]))

## Substraction rule
derivate(::Val{:-}, f::SymType, g::SymType) = Expr(:call, :-, derivate(f), derivate(g))
derivate(n::SubNode) = SubNode(derivate(n[1]), derivate(n[2]))

## Chain rule
derivate(::Val{:*}, f::SymType, g::SymType) = Expr(:call, :+, Expr(:call, :*,derivate(f),g), Expr(:call, :*,derivate(g),f))
derivate(::Val{:*}, f::SymType, n::Number) = derivate(Val(:*), f, n)
derivate(::Val{:*}, n1::Number, n2:: Number) = 0
derivate(::Val{:*}, n::Number, f::SymType) = begin
    if n==0
        return 0
    elseif n==1
        return derivate(f)
    end
    nf = derivate(f)

    if nf isa Expr
        if nf.args[1] == :*
            nf.args[2] *= n
            return nf
        end
    else
        return n*nf
    end

    return Expr(:call, :*, n, nf)

end
derivate(n::ProdNode) = AddNode(ProdNode(derivate(n[1]), n[2]), ProdNode(n[1], derivate(n[2]))

## Power rule
derivate(::Val{:^}, f::SymType, n::Number) = begin
    if iszero(n-1)
        return Expr(:call, :*, n, derivate(f))
    elseif isone(n-1)
        return Expr(:call, :*, n, f, derivate(f))
    end

    return Expr(:call, :*, n, Expr(:call, :^, f::SymType, n-1), derivate(f))
end

## Others 
derivate(ex::Expr) = derivative(ex)
derivate(s::Symbol) = 1

### Cleaning 
cderivate(::Val{:+}, f, g) = Expr(:call, :+, f, g)
cderivate(::Val{:+}, f, n::Number) = iszero(n) ? f : Expr(:call, :+, f, n)
cderivate(::Val{:+}, n::Number, f) = cderivate(Val(:+),f,n)
cderivate(::Val{:+}, n1::Number, n2::Number) = n1 + n2

cderivate(::Val{:-}, f, g) = Expr(:call, :-, f, g)
cderivate(::Val{:-}, f, n::Number) = iszero(n) ? f : Expr(:call, :-, f, n)
cderivate(::Val{:-}, n::Number, f) = iszero(n) ? Expr(:call, :-, f) : Expr(:call, :-, f, n)
cderivate(::Val{:-}, n1::Number, n2::Number) = n1 - n2

cderivate(::Val{:*}, f, g) = Expr(:call, :*, f, g)
cderivate(::Val{:*}, f, n::Number) = cderivate(Val(:*),n,f)
cderivate(::Val{:*}, n::Number, f) = iszero(n) ? :() : Expr(:call, :*, n, f)
cderivate(::Val{:*}, n1::Number, n2::Number) = n1 * n2

cderivate(::Val{:^}, f, g) = Expr(:call, :+, f, g)
cderivate(::Val{:^}, f, n::Number) = iszero(n) ? 1 : (isone(n) ? f : Expr(:call, :^, f, n))
cderivate(::Val{:^}, n1::Number, n2::Number) = n1 ^ n2

function clean_derivative(ex::Expr)
    ch = get_children(ex)
    cderivate(Val(ch[1]), ch[2], ch[3])
end

function derivative(ex::Expr)
    ch = get_children(ex)

    if !is_leave(ch)
        der = derivate(Val(ch[1]), ch[2], ch[3])

        return der
    end

    return :()
end

## Precompiling stuffs
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


eval_func(ex::Expr,v::Number) = begin
    substitute(ex, :x => v) |> eval
end

substitute(n::Number, _) = n
substitute(s::Symbol, sub::Pair{Symbol,<:Number}) = s == sub.first ? sub.second : s
function substitute(ex::Expr, sub)
    Expr(ex.head, [substitute(arg, sub) for arg in ex.args]...)
end