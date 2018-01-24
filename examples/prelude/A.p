type T => java.util.ArrayList<T> as T => A.Array<T>

native A.array : T => (size : Integer) -> res:A.Array<T> where [ size >= 0 and res.size == size ]

native A.range : (mi : Integer, ma : Integer) -> res:A.Array<Integer> # where [ mi <= ma and res.size == (ma - mi)]

native A.get : T => (arr: A.Array<T>, index: Integer) -> p:T # where [ index >= 0 and index < arr.size ]

native A.set : T => (arr: A.Array<T>, index: Integer, value:T) -> p:T

native A.size : T => (arr: A.Array<T>) -> _:Integer

native A.forEach : T => (arr: A.Array<T>, f: (T) -> Void) -> _:A.Array<T>

native A.map : T,R => (arr: A.Array<T>, f: (T) -> R) -> _:A.Array<R>

native A.reduce : T => (arr: A.Array<T>, f: (T,T) -> T) -> _:T