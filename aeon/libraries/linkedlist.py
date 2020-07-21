import copy
from .annotation import aefunction, aedocumentation

''' LinkedList binds in Aeon to Python '''

@aefunction("""type LList[T] {
    size : Integer;
}""", None)

class List(object):
    def __init__(self, element, next):
        self.head = element
        self.next = next
    
    def __str__(self):
        result = ''
        current = self
        while current and current.head:
            result = result + str(current.head) + ", "
            current = current.next
        return '[' + result + ']'


    def __deepcopy__(self):
        result = List(None, None)
        current = result
        itering = self
        while itering and itering.head:
            current.head = copy.deepcopy(itering.head)
            current.next = List(None, None) if itering.next else None
            current = current.next if itering.next else current
            itering = itering.next
        return result

@aefunction('empty_llist[T]() -> {l:LList[T] | l.size == 0};', lambda x : empty_list(x))
def empty_list(ignore):
    return List(None, None)


@aefunction('append_llist[T](x:T, l:LList[T]) -> {l2:LList[T] | l2.size == l.size + 1};', lambda x: lambda l: append(x, l))
def append(x, l):
    result = List(None, None)

    if l.head:
        result.head = copy.deepcopy(l.head)
        if l.next:
            result.next = append(x, l.next)
        else:
            result.next = List(copy.deepcopy(x), None)
    else:
        result.head = copy.deepcopy(x)

    return result


@aefunction('extend_llist[T](l1:LList[T], l2:LList[T]) -> {l3:LList[T] | l3.size == l1.size + l2.size};', lambda l1: lambda l2: extend(l1, l2))
def extend(l1, l2):
    result = List(None, None)
    current = result
    while l1 and l1.head:
        current.head = copy.deepcopy(l1.head)
        current.next = List(None, None) if l1.next else None
        current = current.next if l1.next else current
        l1 = l1.next

    if current.head:
        current.next = List(None, None)
        current = current.next        

    while l2 and l2.head: 
        current.head = copy.deepcopy(l2.head)
        current.next = List(None, None) if l2.next else None
        current = current.next if l2.next else current
        l2 = l2.next

    return result 


@aefunction('insert_llist[T](x:T, l:LList[T], {i:Integer | i <= l.size}) -> {l2:LList[T] | l2.size == l.size + 1};', lambda x: lambda l: lambda i: insert(x, l, i))
def insert(x, l, i):
    if i == 0:
        return extend(List(copy.deepcopy(x), None), l)
    else:
        result = List(copy.deepcopy(x), None)
        result.next = insert(x, l.next, i - 1)
        return result


# Removes the first occurence of the element
@aefunction('remove_llist[T](x:T, l:LList[T]) -> {l2:LList[T] | l2.size <= l.size};', lambda x: lambda l: remove(x, l))
def remove(x, l):
    if not l:
        return None
    if not l.head:
        return List(None, None)
    
    if l.head == x:
        return copy.deepcopy(l.next)
    else:
        if l.next:
            if x == l.next.head:
                return List(copy.deepcopy(x), remove(l, l.next.next)) 
            else:
                return List(copy.deepcopy(x), remove(x, l.next))
        else:
            return List(copy.deepcopy(l.head), None)


# Contains a certain element
@aefunction('contains_llist[T](x:T, l:LList[T]) -> Boolean;', lambda x: lambda l: contains(x, l))
def contains(x, l):
    result = l.head == x
    if result and l.next:
        result = contains(x, l.next)
    return result


# Index of the first occurence of the element
@aefunction('index_llist[T](x:T, l:LList[T]) -> {i:Integer | -1 <= i && i < l.size};', lambda x: lambda l: index(x, l, 0))
def index(x, l, i):
    if x == l.head:
        return i
    else:
        if l.next:
            return index(x, l.next, i + 1)
        else:
            return -1


# Amount of times an element occurs 
@aefunction('count_llist[T](x:T, l:LList[T]) -> Integer;', lambda x: lambda l: count(x, l))
def count(x, l):
    result = (int) (x == l.head)
    if l.next:
        result += count(x, l.next)
    return result

'''
# Reverses a list 
@aefunction('reverse[T](l:LList[T]) -> LList[T] = native;', lambda l: reverse(l))
def reverse(l):
    pass
'''

# Check if any element of the list respects a predicate 
@aefunction('exists_llist[T](f:(x:T -> Boolean), l:LList[T]) -> Boolean;', lambda f: lambda l: exists(f, l))
def exists(f, l):
    if not l.head:
        return False
    result = f(l.head)
    if not result and l.next:
        result = exists(f, l.next)
    return result


# Check if all element of the list respects a predicate 
@aefunction('forall_llist[T](f:(x:T -> Boolean), l:LList[T]) -> Boolean;', lambda f: lambda l: forall(f, l))
def forall(f, l):
    if not l.head:
        return False
    result = f(l.head)
    if result and l.next:
        result = exists(f, l.next)
    return result

# Check if any element of the list respects a predicate 
@aefunction('filter_llist[T](f:(x:T -> Boolean), l:LList[T]) -> LList[T];', lambda f: lambda l: filter(f, l))
def filter(f, l):
    if not l.head:
        return List(None, None)
    if f(l.head):
        result = List(copy.deepcopy(l.head), None)
    else:
        result = None
    
    if l.next:
        next_list = filter(f, l.next)
    else:
        next_list = None

    if not result and not next_list:
        result = List(None, None)
    elif not result:
        result = next_list
    elif not next_list:
        pass
    else:
        result.next = next_list
    return result


# Map each element
@aefunction('map_llist[T](f:(x:T -> T), l:LList[T]) -> {l2:LList[T] | l.size == l2.size};', lambda f: lambda l: map(f, l))
def map(f, l):
    if not l.head:
        return List(None, None)
    
    result = List(f(copy.deepcopy(l.head)), None)

    if l.next:
        result.next = map(f, l.next)

    return result


# Size of the list 
@aefunction('length_llist[T](l:LList[T]) -> {i:Integer | i == l.size};', lambda l: length(l))
def length(l):
    if not l or not l.head:
        return 0
    return 1 + length(l.next)


def clone(llist):
    result = List(None, None)
    if llist.head:
        result.head = copy.deepcopy(llist.head)
        result.next = None if llist.next is None else clone(llist.next)
    return result
