from aeon.automatic.selection import select
from aeon.automatic.crossover.crossover import regular_crossover

from aeon.automatic.parameters import POPULATION_SIZE, MAX_DEPTH

# Choose the strategy for the crossover
def crossover(population, genetics):

    offspring = list()

    hole_types = [hole for ctx, hole in genetics.holes]

    for _ in range(POPULATION_SIZE):
        # Select parents for crossover
        parent1 = select(population)
        parent2 = select(population)

        # Crosses both parents according to a crossover strategy
        individual = regular_crossover(MAX_DEPTH, parent1, parent2, hole_types)

        offspring.append(individual)

    return offspring