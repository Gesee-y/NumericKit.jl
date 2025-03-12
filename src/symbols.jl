############ managing functions symbols ################

#### First, we make a basic tree system 

get_children(A::AbstractArray) = A
get_children(e::Expr) = e.args
get_children(n) = ()

is_leave(n) = isempty(get_children(n))

### Managing Symbols
is_leave(n) = isempty(get_children(n))

add_deriv(f,g) = Expr(:call, :+, derivative(f), derivative(g))

derivate(n::Number) = 0
derivate(::Val{:+}, f, g) = Expr(:call, :+, derivate(f), derivate(g))
derivate(::Val{:-}, f, g) = Expr(:call, :-, derivate(f), derivate(g))
derivate(::Val{:*}, f, g) = Expr(:call, :+, Expr(:call, :*,derivate(f),g), Expr(:call, :*,derivate(g),f))
derivate(::Val{:*}, f, n::Number) = Expr(:call, :*, n, derivate(f))
derivate(::Val{:*}, n::Number, f) = Expr(:call, :*, n, derivate(f))
derivate(::Val{:^}, f, n::Number) = begin
    if iszero(n-1)
        return Expr(:call, :*, n, derivate(f))
    elseif isone(n-1)
        return Expr(:call, :*, n, f, derivate(f))
    end

    return Expr(:call, :*, n, Expr(:call, :^, f, n-1), derivate(f))
end
derivate(ex::Expr) = derivative(ex)
derivate(s::Symbol) = 1

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

        return clean_derivative(der)
    end
    
    return :()
end

eval_func(ex::Expr,v) = begin
   for i in eachindex(ex.args)
       arg = ex.args[i]
       if arg == :x
           ex.args[i] = v
       elseif arg isa Expr
           eval_func(arg,v)
       end
   end

   eval(ex)
end
