import prelude.J

import fibonacci.simple_fib
import fibonacci.par_fib

main : (args:Array<String>) -> _:Void {
   n = 30
   J.out(J.timeit( () -> fib(n) ))
   J.out(J.timeit( () -> fibp(n) ))
}
