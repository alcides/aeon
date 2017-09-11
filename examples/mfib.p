import prelude.J
import prelude.F

fib : ( n:Integer ) -> _:Integer with [ time(10) and memory(20) ] {
   J.out(1)
   J.iif(n < 2, () -> 1, () -> fib(n-1) + fib(n-2) )
}

fib : ( n:Integer ) -> _:Integer with [ time(10) and memory(20) ] {
   J.out(2)
   J.iif(n < 2, () -> { 1 }, () -> {
      a = F.future( () -> fib(n-1))
      b = F.future( () -> fib(n-2))
      F.get(a)+F.get(b)
   })
}


main : (args:Array<String>) -> _:Void {
   n = 30
   J.out(J.timeit( () -> fib(n) ))
}
