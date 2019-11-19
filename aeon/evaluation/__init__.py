from .evaluators.evaluator import Evaluator

from aeon.frontend2 import expr, typee

ex = expr.parse_strict
ty = typee.parse_strict

RUNS = 10
MAX_TREE_DEPTH = 3
POPULATION_SIZE = 100
OUTPUT_PATH = Evaluator().FOLDER_PATH + '/output/'

typees = [
    ty('Integer'),
]
