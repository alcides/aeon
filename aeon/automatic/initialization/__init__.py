from aeon.automatic.initialization.full import full
from aeon.automatic.initialization.grow import grow
from aeon.automatic.initialization.ramped import ramped

from aeon.automatic.parameters import MAX_DEPTH, POPULATION_SIZE

# Chooses the approach we'll be using for initialization
def initialize_population(genetics):
    return ramped(genetics.holes, MAX_DEPTH, POPULATION_SIZE)