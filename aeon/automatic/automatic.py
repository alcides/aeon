import random
import logging

from aeon.automatic.parameters import *

from aeon.automatic.mutation import mutate
from aeon.automatic.selection import select
from aeon.automatic.crossover import crossover
from aeon.automatic.evaluation import evaluate
from aeon.automatic.initialization import initialize_population


class Genetics(object):
    def __init__(self, declaration, holes, eval_ctx, ctx, fitness_functions):
        self.declaration = declaration
        self.holes = holes
        self.eval_ctx = eval_ctx
        self.type_context = ctx
        self.fitness_functions = fitness_functions

    def evolve(self):

        # Initialize and evaluate the population
        population = initialize_population(self)
        population = evaluate(population, self)
        print(population)
        '''
        for generation in range(1, MAX_GENERATIONS):

            logging.debug("Generation {generation}")

            # Create the new population
            offspring = list()

            # Crossover the parents and obtain the offspring
            logging.debug("Crossing the population...")
            offspring = crossover(population, self)
            
            # Mutate the individuals and obtain the offspring
            logging.debug("Mutating the population...")
            offspring = mutate(offspring, self)

            # Evaluate the offspring
            logging.debug("Evaluating the population...")
            offspring = evaluate(offspring, self)

            # Transition to the new population
            population = offspring

            # Hold condition
            best_individuals = [x for x in population if sum(x.fitness) == 0.0]

            if best_individuals:
                population = best_individuals
                break
        '''
        return random.choice(population)
