import builtins
from .annotation import aefunction, aedocumentation

@aefunction('print[T]: (a:T) -> {b:T | a == b} = native;', lambda x: print(x))
def print(x):
    builtins.print('PRINT:', x)
    return x


@aefunction('id[T]: (a:T) -> {b:T | a == b} = native;', lambda x: id(x))
def id(value):
    return value

# TODO:
@aefunction('forall[T]: (a:List[T], f:(T -> Boolean)) -> c:Boolean = native;', lambda x: lambda f: forall(x, f))
def forall(list, function):
    all(map(lambda x: function(x), lista))

# TODO:
@aefunction('exists[T]: (a:List[T], f:(T -> Boolean)) -> Boolean = native;', lambda x: lambda f: exists(x, f))
def exists(list, function):
    any(map(lambda x: function(x), lista))


@aefunction('fix[T]: (x:(T -> T)) -> T = native;', lambda f: fix(f))
def fix(function):
    function(lambda x: fix(function)(x))

@aefunction('getVoid() -> Void = native;', lambda x: getVoid(x)):
def getVoid(ignore):
    return None