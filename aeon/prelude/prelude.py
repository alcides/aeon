from aeon.frontend.parser import parse_type


def p(x):
    print(x)
    return 0


prelude = [
    ("print", "(x:String) -> Int", p),
    ("==", "(x:Int) -> (y:Int) -> Bool", lambda x: lambda y: x == y),
    ("!=", "(x:Int) -> (y:Int) -> Bool", lambda x: lambda y: x != y),
    ("<", "(x:Int) -> (y:Int) -> Bool", lambda x: lambda y: x < y),
    ("<=", "(x:Int) -> (y:Int) -> Bool", lambda x: lambda y: x <= y),
    (">", "(x:Int) -> (y:Int) -> Bool", lambda x: lambda y: x > y),
    (">=", "(x:Int) -> (y:Int) -> Bool", lambda x: lambda y: x >= y),
    ("+", "(x:Int) -> (y:Int) -> Int", lambda x: lambda y: x + y),
    ("-", "(x:Int) -> (y:Int) -> Int", lambda x: lambda y: x - y),
    ("*", "(x:Int) -> (y:Int) -> Int", lambda x: lambda y: x * y),
    ("/", "(x:Int) -> (y:Int) -> Int", lambda x: lambda y: x / y),
]

typing_vars = {}
evaluation_vars = {}

for (n, ty, ex) in prelude:
    typing_vars[n] = parse_type(ty)
    evaluation_vars[n] = ex
