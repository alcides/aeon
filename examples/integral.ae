import prelude.J
import prelude.A

f : (x:Double) -> _:Double {
  x * x
}

# computes the integral of f from mi to ma with n trapezoids
integral : (mi:Double, ma:Double, n:Integer) -> _:Double {
  a = A.range(0, n)
  step = (ma-mi) / n
  b = A.map(a, (i:Integer) -> {
    x1 = mi + (i * step)
    x2 = mi + ((i + 1) * step)
    (f(x1) + f(x2)) * (step * 0.5)
  })
  A.reduce(b, (x:Double, y:Double) -> x+y)
}

main : (args:Array<String>) -> _:Void {
   n = 10000000
   J.out(J.timeit( () -> integral(0.0, 10.0, n) ))
}
