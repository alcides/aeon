import ..prelude.J

# Fibonacci

fib : ( n:Integer ) -> _:Integer with [ time(10) and memory(20) ] {
   J.iif(n < 2, () -> 1, () -> fib(n-1) + fib(n-2) )
}
