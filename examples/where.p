import prelude.J
import prelude.A


plus : (n:Integer) -> npo:Integer where [ npo = n + 1 ] {
   n +1
}


main : (args:Array<String>) -> _:Void {
   a = A.array(10)
   b = 10
   J.out(A.get(a, b))
   c = plus(b)
   J.out(A.get(a, c))
}
