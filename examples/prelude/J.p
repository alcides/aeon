
native J.iif : T => (_:Boolean, _: () -> T, _:() -> T) -> _:T # where T <: Object

native J.out : (_:Object) -> _:Object # with IO()

native J.noop : (_:Object) -> _:Void

native J.timeit : T => (_:() -> T) -> _:T # with IO()