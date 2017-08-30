# Fibonacci

fib : ( n:Integer ) -> _:Integer {
   J.iif(n < 2, -> 1, -> fib(n-1) + fib(n-2) )
}
