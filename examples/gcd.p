import prelude.J


gcd : (i:Integer, j:Integer) -> k:Integer where [ (i % k) == 0 and (j % k) == 0 ] {
   J.iif(j == 0, () -> i, () -> gcd(j, i % j))
}


main : (args:Array<String>) -> _:Void {
   J.out(gcd(55,100))
}