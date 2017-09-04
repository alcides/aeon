import prelude.J


main : (args:Array<String>) -> _:Void {
   supplier = () -> 1
   unaryoperator = (a:Integer) -> 1
   predicate = (a:Integer) -> true
   function = (a:Integer) -> 2.0
   J.out(1)
}
