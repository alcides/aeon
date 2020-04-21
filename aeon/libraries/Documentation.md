## Libraries

To more easily allow the interaction of the user with the language, **Æon** provides different kinds of implemented [**libraries**](aeon/libraries).

#### Math
```haskell 
minimum[T](T, T) -> T;
```
```haskell 
maximum[T](T, T) -> T;
```
```haskell 
absolute[T](T) -> T;
```
```haskell 
ceil(Double) -> Integer;
```
```haskell 
floor(Double) -> Integer;
```
```haskell 
power[T](T, T) -> T;
```
```haskell 
squareroot[T](x:T) -> {y:Double | x - y * y < 0.0001};
```

#### Strings
```haskell 
equals(String, String) -> Boolean;
```
```haskell 
concat(String, String) -> String;
```
```haskell 
ascii_code({s:String | s.size == 1}) -> Integer; 
```
```haskell 
ascii_letters() -> {s:String | s.size == 52};
```
```haskell 
charAt(s:String, {i:Integer | i >= 0 && i < s.size}) -> Integer; 
```
```haskell 
size(String) -> Integer;
```
```haskell 
replace(String, String, String) -> String;
```
```haskell 
substring(String, String) -> Boolean;
```
```haskell 
head({s:String | s.size > 0}) -> {s2:String | s2.size == 1};
```
```haskell 
tail({s:String | s.size > 0}) -> {s2:String | s2.size == s.size - 1}; 
```
```haskell 
count({s:String | s.size == 1}, s2:String) -> Integer;
```
```haskell 
forall((String -> Boolean), String) -> Boolean
```

#### Lists
```haskell 
empty_list[T]() -> {l:List[T] | l.size == 0};
```
```haskell 
range_list[T](min:Integer, max:Integer) -> {l:List | l.size == (max - min)};
```
```haskell 
extend[T](l1:List[T], l2:List[T]) -> {l3:List[T] | l3.size == l1.size + l2.size};
```
```haskell 
insert[T](T, l1:List[T], {i:Integer | i >= 0 && i < l1.size} -> {l2:List[T] | l2.size == l1.size + 1};
```
```haskell 
remove[T](T, l1:List[T]) -> {l2:List[T] | l2.size <= l1.size};
```
```haskell 
contains[T](T, List[T]) -> Boolean;
```
```haskell 
index[T](T, l:List[T]) -> {i:Integer | -1 <= i && i <= l.size};
```
```haskell 
count[T](T, List[T]) -> Integer;
```
```haskell 
reverse[T](l1:List[T]) -> {l2:List[T] | l1.size == l2.size};
```
```haskell 
length[T](l:List[T]) -> {i:Integer | i == l.size};
```
```haskell 
head[T]({l:List[T] | l.size > 0}) -> T;
```
```haskell 
tail[T]({l1:List[T] | l.size > 0}) -> {l2:List[T] | l2.size == l1.size - 1};
```
```haskell 
elemAt[T](Integer, List[T]) -> T;
```
```haskell 
exists[T]((T -> Boolean), List[T]) -> Boolean;
```
```haskell 
forall[T]((T -> Boolean), List[T]) -> Boolean;
```
```haskell 
filter[T]((T -> Boolean), l1:List[T]) -> {l2:List[T] | l2.size <= l1.size};
```
```haskell 
map[T, K]((T -> K), List[T]) -> List[K];
```
```haskell 
reduce[T, K]((T -> (K -> K)), List[T]) -> K;
```