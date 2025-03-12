using NumericKit

function main()
    ex = :(2x^5 - 3x + 2)
    println(typeof(ex))
    println(ex.head)
    println(get_children(ex))

    @time der = derivative(ex)
    @time der2 = derivative(der)
    println("first derivative : ", der)
    println("second derivative : ", der2)

    println(eval_func(der,0))
    println("first derivative : ", der)
end

main()
