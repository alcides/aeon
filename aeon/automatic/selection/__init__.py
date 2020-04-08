from aeon.automatic.selection.roulette import roulette
from aeon.automatic.selection.lexicase import e_lexicase
from aeon.automatic.selection.random_selection import random_selection

# Applies a selection strategy to obtain an individual from a population
def select(population):
    return e_lexicase(population)