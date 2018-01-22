import ..prelude.F

fibp : ( n:Integer ) -> _:Integer {
   J.iif(n < 2, () -> { 1 }, () -> {
      b = F.future( () -> fibp(n-2))
      fibp(n-1) + F.get(b)
   })
}
