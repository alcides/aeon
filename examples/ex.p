import prelude.J

type Integer as Nat where [ self >= 0 ]
type Integer as Neg where [ self < 0 ]

plus : (n:Nat) -> npo:Nat where [ npo == (n + 1) ] {
   n + 1
}

main : (args:Array<String>) -> _:Void {
   n = plus(plus(0))
   J.out(n)
}
