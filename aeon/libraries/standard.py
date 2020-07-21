import builtins
from .annotation import aefunction, aedocumentation

@aefunction('print[T](a:T) -> {b:T | a == b};')
def print(x):
    builtins.print('PRINT:', x)
    return x


@aefunction('id[T](a:T) -> {b:T | a == b};')
def id(value):
    return value

# TODO:
@aefunction('forall[T](a:List[T], f:(x:T -> Boolean)) -> Boolean;')
def forall(list, function):
    all(map(lambda x: function(x), lista))

# TODO:
@aefunction('exists[T](a:List[T], f:(x:T -> Boolean)) -> Boolean;')
def exists(list, function):
    any(map(lambda x: function(x), lista))


@aefunction('fix[T](f:(x:T -> T)) -> T;')
def fix(function):
    function(lambda x: fix(function)(x))

@aefunction('getVoid() -> Void;')
def getVoid(ignore):
    return None