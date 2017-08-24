# Fibonacci

fib : ( n:Integer ) -> _:Integer {
   J.iif(n < 2, -> 1, -> fib(n-1) + fib(n-2) )
}

fibp : ( n:Integer ) -> _:Integer {
   J.iif(n < 2, -> { 1 }, -> {
      let a = F.future( -> fib(n-1))
      let b = fib(n-2)
      F.get(a)+b
   })
}

main : (n:Array<String>) -> _:Void {
   J.out(fibp(8))
}
