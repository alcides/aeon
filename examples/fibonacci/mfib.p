import ..prelude.J
import ..prelude.F


# 10.795533183 s
fib : ( n:Integer ) -> _:Integer with [ time(n * 0.001) and heap(20) ] {
   J.iif(n < 2, () -> 1, () -> fib(n-1) + fib(n-2) )
}

# > 1 min
fib : ( n:Integer ) -> _:Integer with [ time(((n * 0.001) / F.processors ) + 0.004) and heap(40) ] {
   J.iif(n < 2, () -> { 1 }, () -> {
      b = F.future( () -> fib(n-2))
      fib(n-1) + F.get(b)
   })
}

# multiversioning:

main : (args:Array<String>) -> _:Void {
   n = 44
   J.out(J.timeit( () -> fib.1(n) ))
   J.out(J.timeit( () -> fib.2(n) ))
   J.out(J.timeit( () -> fib(n) ))
}
