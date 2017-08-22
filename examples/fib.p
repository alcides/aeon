# Fibonacci

fib : ( n:Integer ) -> _:Integer {
   J.iif(n < 2, -> 1, -> fib(n-1) + fib(n-2) )
}

fibp : ( n:Integer ) -> _:Integer {
   J.iif(n < 2, -> { 1 }, -> {
      J.out(10)
      2
   })
}

main : (n:Array<String>) -> _:Void {
   J.out(fibp(8))
}
