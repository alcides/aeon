import ..prelude.Math

type Integer as Nat where [ self >= 0 ]
type Integer as Neg where [ self < 0 ]


f1 : () -> o:Integer where [ o == 1 ] {
   1
}

f2 : (a:Nat) -> o:Integer where [ o == (a - 1) ] {
   b = 1
   c = a - b
}

main : (args:Array<String>) -> _:Void { 
   a : Nat = 0
   b : Neg = -1
}
