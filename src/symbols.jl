############ managing functions symbols ################

#### First, we make a basic tree system 

get_children(A::AbstractArray) = A
get_children(e::Expr) = e.args

is_leave(n) = isempty(get_children(n))

### Managing symbols