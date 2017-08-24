# Fibonacci

fib : ( n:Integer ) -> _:Integer {
   J.iif((n < 2) || ((n < 1) && (n > 0)), -> 1, -> fib(n-1) + fib(n-2) )
}

fibp : ( n:Integer ) -> _:Integer {
   J.iif(n < 2, -> { 1 }, -> {
      let a = F.future( -> fib(n-1))
      let b = fib(n-2)
      F.get(a)+b
   })
}

main : (args:Array<String>) -> _:Void {
   let n = 12
   J.out(0)
   J.out(J.timeit( -> fib(n)))
   J.out(1)
   J.out(J.timeit( -> fibp(n)))
}
