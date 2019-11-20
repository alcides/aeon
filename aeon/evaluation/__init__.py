from .evaluators.evaluator import Evaluator

from aeon.frontend2 import expr, typee

ex = expr.parse_strict
ty = typee.parse_strict

RUNS = 10
MAX_TREE_DEPTH = 4
POPULATION_SIZE = 100
OUTPUT_PATH = Evaluator().FOLDER_PATH + '/output/'

typees = [
    ty('Integer'),
    ty('Double'),
    ty('String'),
    ty('Boolean'),
    #ty('(x:Integer) -> {x:Integer where (x > 0)}'),
    #ty('(x:{y:Integer where (y > 0)}) -> {z:Integer where (z > x)}')
]
