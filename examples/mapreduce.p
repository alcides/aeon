import prelude.J
import prelude.A


main : (args:Array<String>) -> _:Void { 
   a = A.range(0,100)
   b = A.map(a, (i:Integer) -> i*i)
   c = A.reduce(b, (i:Integer, j:Integer) -> i + j)
   J.out(c)
}