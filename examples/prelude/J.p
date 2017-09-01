
native J.iif : T => (_:Boolean, _: () -> T, _:() -> T) -> _:T # where T <: Object

native J.out : (_:Integer) -> _:Integer # with IO()

native J.timeit : (_:() -> Integer) -> _:Integer # with IO()
