import copy
import builtins
import functools
from .annotation import aefunction, aedocumentation

''' List binds in Aeon to Python '''

@aefunction("""type List[T] {
    size : Integer;
}""")
class List(object):
    def __init__(self):
        pass

# Empty list
@aefunction('empty_list[T]() -> {l:List[T] | l.size == 0};')
def empty_list(ignore):
    return []

# Range: returns a list of Integers
@aefunction('range_list[T](min:Integer, max:Integer) -> {l:List[Integer] | l.size == (max - min)};')
def range_list(minimum, maximum):
    return list(builtins.range(minimum, maximum))

# Append an element to the list
@aefunction('append_list[T](x:T, l:List[T]) -> {l2:List[T] | l2.size == l.size + 1};')
def append(x, l):
    return l + [x]

# Extend the list with another list
@aefunction('extend_list[T](l1:List[T], l2:List[T]) -> {l3:List[T] | l3.size == l1.size + l2.size};')
def extend(l1, l2):
    return l1 + l2

# Insert at a specific position
@aefunction('insert_list[T](x:T, l:List[T], i:{i:Integer | i <= l.size}) -> {l2:List[T] | l2.size == l.size + 1};')
def insert(x, l, i):
   return l[0:i] + [x] + l[i:]

# Removes the first occurence of the element
@aefunction('remove_list[T](x:T, l:List[T]) -> {l2:List[T] | l2.size <= l.size};')
def remove(x, l):
    if x not in l:
        return copy.deepcopy(l)
    return l[0:l.index(x)] + l[l.index(x) + 1:]

# Contains a certain element
@aefunction('contains_list[T](x:T, l:List[T]) -> Boolean;')
def contains(x, l):
    return x in l

# Index of the first occurence of the element
@aefunction('index_list[T](x:T, l:List[T]) -> {i:Integer | -1 <= i && i < l.size};')
def index(x, l):
    return l.index(x)

# Amount of times an element occurs 
@aefunction('count_list[T](x:T, l:List[T]) -> Integer;')
def count(x, l):
    return l.count(x)

# Reverses a list 
@aefunction('reverse_list[T](l:List[T]) -> List[T];')
def reverse(l):
    return list(reversed(l))

# Check if any element of the list respects a predicate 
@aefunction('exists_list[T](f:(x:T -> Boolean), l:List[T]) -> Boolean;')
def exists(f, l):
    return any(f(x) for x in l)

# Check if all element of the list respects a predicate 
@aefunction('forall_list[T](f:(x:T -> Boolean), l:List[T]) -> Boolean;')
def forall(f, l):
    return all(f(x) for x in l)

# Check if any element of the list respects a predicate 
@aefunction('filter_list[T](f:(x:T -> Boolean), l:List[T]) -> List[T];')
def filter(f, l):
    return list(builtins.filter(f, l))
    
# Map each element
@aefunction('map_list[T, K](f:(x:T -> K), l:List[T]) -> {l2:List[K] | l.size == l2.size};')
def map(f, l):
    return list(builtins.map(f, l))

# Element at a certain position
@aefunction('elemAt_list[T](i:Integer, l:List[T]) -> T;')
def elemAt(i, l):
    return l[i]

# Reduce
@aefunction('reduce_list[X, Y](f:(x:X -> (y:Y -> Y)), l:{l:List[X] | l.size > 0}) -> X;')
def reduce_list(f, l):
    return functools.reduce(lambda x, y: f(x)(y), l)

# Size of the list 
@aefunction('length_list[T](l:List[T]) -> {i:Integer | i == l.size};')
def length(l):
    return len(l)

# Head of the list
@aefunction('head_list[T](l:{l:List[T] | l.size > 0}) -> T;')
def head(l):
    return l[0]

# Tail of the list 
@aefunction('tail_list[T](l:{l:List[T] | l.size > 0}) -> {l2:List[T] | l2.size == l.size - 1};')
def tail(l):
    return l[1:]


