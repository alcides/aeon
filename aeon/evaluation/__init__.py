from .evaluators.evaluator import Evaluator

from aeon.frontend_core import expr, typee
from aeon.ast import Application, Var, If, Literal, TApplication
from aeon.types import t_i

ex = expr.parse
ty = typee.parse

RUNS = 1
MIN_TREE_DEPTH = 2
MAX_TREE_DEPTH = 5
POPULATION_SIZE = 100
OUTPUT_PATH = Evaluator().FOLDER_PATH + 'output/'

typees = [
    (ty('Integer'), 'Integer', lambda x: x),
    (ty('{x:Integer where (x > 0)}'), 'Natural', lambda x: x),
    (ty('{x:Integer where ((x % 4) == 0 )}'), 'Multiple of 4', lambda x: x),
    (ty('{x:Integer where ((x > 0) && (x < 10))}'), 'Smaller than 10 Natural',
     lambda x: x),
    (ty('Double'), 'Double', lambda x: x),
    (ty('String'), 'String', lambda x: Application(Var('string_length'), x)),
    (ty('Boolean'), 'Boolean',
     lambda x: If(x, Literal(1, t_i), Literal(0, t_i))),
    (ty('(x:Integer) -> Integer'), 'Abstract Integer',
     lambda x: Application(x, Literal(42, t_i))),
    (ty('(x:Integer) -> {x:Integer where (x > 0)}'),
     'Refined Abstract Integer', lambda x: Application(x, Literal(42, t_i))),
    (ty('(a:Integer) -> (b:Integer) -> Integer'),
     'Refined Double Abstract Integer',
     lambda x: Application(Application(x, Literal(42, t_i)), Literal(42, t_i))
     ),
    (ty('(x:{y:Integer where (y > 0)}) -> {z:Integer where (z > x)}'),
     'Refined Input-Output', lambda x: Application(x, Literal(42, t_i))),
    #(ty('(T:*) => (x:T) -> T'), lambda x: Application(x, Literal(42, t_i))),
    #(ty('(T:*) => (x:T) -> Integer'), lambda x: Application(TApplication(x, t_i), Literal(42, t_i))),
]
