import random

from aeon.automatic.parameters import *

from aeon.automatic.fitness import evaluate
from aeon.automatic.mutation import mutation
from aeon.automatic.crossover import crossover
from aeon.automatic.selection import selection
from aeon.automatic.initialization import initialize_population

class Genetics(object):

    def __init__(self, declaration, holes, eval_ctx, ctx, fitness_functions):
        self.declaration = declaration
        self.holes = holes
        self.eval_ctx = eval_ctx
        self.type_context = ctx
        self.fitness_functions = fitness_functions

    def evolve(self):

        # Initialize, evaluate and sort the population
        population = initialize_population()

        for generation in range(1, MAX_GENERATIONS):

            print("Generation", generation)

            # Create the new population
            offspring = list()

            # Crossover the parents and obtain the offspring
            offspring = crossover(population, self)

            # Mutate the individuals and obtain the offspring
            offspring = mutate(offspring, self)

            # Evaluate the offspring
            offspring = evaluate(offspring, self)

            # Transition to the new population
            population = offspring

            # Hold condition
            best_individuals = [x for x in population if sum(x.fitness) == 0.0]

            if best_individuals:
                population = best_individuals
                break

        return random.choice(population)
