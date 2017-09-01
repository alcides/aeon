type T => aeminium.runtime.futures.Future<T> as T => Future<T>
type Integer as Nat

native F.future : T => (_:() -> T) -> _:Future<T>

native F.get : T => (_:Future<T>) -> _:T
