import prelude.J
import prelude.A

type Integer as Nat where [ self >= 0 ]
type Integer as Neg where [ self < 0 ]

plus : (n:Nat) -> npo:Integer where [ npo == (n + 1) ] {
   n + 1
}


fun : (i:Integer, j:Integer) -> _:Integer where [ (i + j) < 10 and j > 0 ] {
   i + j
}

 main : (args:Array<String>) -> _:Void { 
   a = A.array(10, 0)
   b = -10
   #J.out(A.get(a, b))
   c = plus(b)
   #J.out(A.get(a, c))

   fun(1,2)
   fun(6,2)
   #fun(6,5) -- causes type error
}
