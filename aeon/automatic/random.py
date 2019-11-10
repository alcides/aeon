import aeon.synthesis as synthesis

from .gen_prog import *
from .utils import replaceHoles


class Random(GenProg):
    def __init__(self, definition, function, holes):
        super(Random, self).__init__()
        self.definition = definition
        self.function = function
        self.holes = holes

    def crossover(self):
        pass

    def mutate(self):
        pass

    def evaluate_fitness(self):
        pass

    def run(self):
        population = generate_population()
        return population

    # Generates the initial population
    def generate_population(self):

        population = []

        for i in range(self.POPULATION_SIZE):
            individual_holes = [
                synthesis.se(ctx, hole, self.DEPTH) for ctx, hole in self.holes
            ]
            individual = self.function.copy()
            individual.replace_holes(individual, individual_holes)
            population.append(individual)

        return population
