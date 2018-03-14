import prelude.J

type Integer as Nat where [ self >= 0 ]
type Integer as Neg where [ self < 0 ]


native Math.sqrt : (x:Double) -> y:Double where [ x >= 0 and y >= 0 ]



main : (args:Array<String>) -> _:Void {
   b = Math.sqrt(3.0)
   c = Math.sqrt(b)
   J.out(c)
}



