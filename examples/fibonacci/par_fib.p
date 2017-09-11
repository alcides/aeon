import ..prelude.F

fibp : ( n:Integer ) -> _:Integer {
   J.iif(n < 2, () -> { 1 }, () -> {
      a = F.future( () -> fibp(n-1))
      b = F.future( () -> fibp(n-2))
      F.get(a)+F.get(b)
   })
}
