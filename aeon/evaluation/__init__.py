from .evaluators.evaluator import Evaluator

from aeon.frontend2 import expr, typee
from aeon.ast import Application, Var, If, Literal, TApplication
from aeon.types import t_i

ex = expr.parse_strict
ty = typee.parse_strict

RUNS = 1
MIN_TREE_DEPTH = 2
MAX_TREE_DEPTH = 15
POPULATION_SIZE = 10  #1000
OUTPUT_PATH = Evaluator().FOLDER_PATH + '/output/'

typees = [
    (ty('Integer'), lambda x: x),
    (ty('{x:Integer where (x > 0)}'), lambda x: x),
    (ty('{x:Integer where ((x % 4) == 0 )}'), lambda x: x),
    (ty('{x:Integer where ((x > 0) && (x < 10))}'), lambda x: x),
    (ty('Double'), lambda x: x),
    (ty('String'), lambda x: Application(Var('string_length'), x)),
    (ty('Boolean'), lambda x: If(x, Literal(1, t_i), Literal(0, t_i))),
    (ty('(x:Integer) -> Integer'), lambda x: Application(x, Literal(42, t_i))),
    (ty('(x:Integer) -> {x:Integer where (x > 0)}'),
     lambda x: Application(x, Literal(42, t_i))),
    (ty('(a:Integer) -> (b:Integer) -> Integer'),
     lambda x: Application(Application(x, Literal(42, t_i)), Literal(42, t_i))
     ),
    (ty('(x:{y:Integer where (y > 0)}) -> {z:Integer where (z > x)}'),
     lambda x: Application(x, Literal(42, t_i))),
    #(ty('(T:*) => (x:T) -> T'), lambda x: Application(x, Literal(42, t_i))),
    #(ty('(T:*) => (x:T) -> Integer'), lambda x: Application(TApplication(x, t_i), Literal(42, t_i))),
]
