import random

from aeon.automatic.mutation.mutate import regular_mutation

from aeon.automatic.parameters import MAX_DEPTH, MUTATION_RATE

# Choose the strategy for the crossover
def mutate(population, genetics):

    offspring = list()

    hole_types = [hole for ctx, hole in genetics.holes]

    for individual in population:
        # Mutate individuals according to the mutation rate
        if random.random() < MUTATION_RATE:
            individual = regular_mutation(MAX_DEPTH, individual, hole_types)
        
        offspring.append(individual)

    return offspring

