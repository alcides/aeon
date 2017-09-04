type T => java.util.ArrayList<T> as T => A.Array<T>

native A.array : T => (size : Integer) -> _:A.Array<T> where [ size >= 0 ]

native A.get : T => (arr: A.Array<T>, index: Integer) -> p:T

