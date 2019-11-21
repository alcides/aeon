from .evaluators.evaluator import Evaluator

from aeon.frontend2 import expr, typee
from aeon.ast import Application, Var, If, Literal, TApplication
from aeon.types import t_i

ex = expr.parse_strict
ty = typee.parse_strict

RUNS = 1
MIN_TREE_DEPTH = 2
MAX_TREE_DEPTH = 5
POPULATION_SIZE = 50  #1000
OUTPUT_PATH = Evaluator().FOLDER_PATH + '/output/'

typees = [
    (ty('Integer'), 'Integer', lambda x: x),
    (ty('{x:Integer where (x > 0)}'), 'Natural', lambda x: x),
    (ty('{x:Integer where ((x % 4) == 0 )}'), 'Type 1', lambda x: x),
    (ty('{x:Integer where ((x > 0) && (x < 10))}'), 'Type 2', lambda x: x),
    (ty('Double'), 'Double', lambda x: x),
    (ty('String'), 'String', lambda x: Application(Var('string_length'), x)),
    (ty('Boolean'), 'Boolean', lambda x: If(x, Literal(1, t_i), Literal(0, t_i))),
    (ty('(x:Integer) -> Integer'), 'Type 3', lambda x: Application(x, Literal(42, t_i))),
    (ty('(x:Integer) -> {x:Integer where (x > 0)}'), 'Type 4',
     lambda x: Application(x, Literal(42, t_i))),
    (ty('(a:Integer) -> (b:Integer) -> Integer'), 'Type 5',
     lambda x: Application(Application(x, Literal(42, t_i)), Literal(42, t_i))
     ),
    (ty('(x:{y:Integer where (y > 0)}) -> {z:Integer where (z > x)}'), 'Type 6',
     lambda x: Application(x, Literal(42, t_i))),
    #(ty('(T:*) => (x:T) -> T'), lambda x: Application(x, Literal(42, t_i))),
    #(ty('(T:*) => (x:T) -> Integer'), lambda x: Application(TApplication(x, t_i), Literal(42, t_i))),
]
