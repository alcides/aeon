import builtins
from .standard import aetype

@aetype('print<T>: (a:T) -> {b:T | a == b} = native;')
def print(x):
    builtins.print('PRINT:', x)
    return x

@aetype('abs<T>: (a:T) -> {b:T | b == (a >= 0 ? a : -a)} = native;')
def abs(value):
    return builtins.abs(value)

@aetype('id<T>: (a:T) -> {b:T | a == b} = native;')
def id(value):
    return value

# TODO:
@aetype('forall<T>: (a:List<T>, f:(T -> Boolean)) -> c:Boolean = native;')
def forall(list, function):
    all(map(lambda x : function(x), lista))

# TODO:
@aetype('exists<T>: (a:List<T>, f:(T -> Boolean)) -> Boolean = native;')
def exists(list, function):
    any(map(lambda x : function(x), lista))

@aetype('fix<T>: (x:(T -> T)) -> T = native;')
def fix(function):
    function(lambda x: fix(function)(x))