import aeon2.synthesis as synthesis

from .genProg import *
from .utils import replaceHoles


class Random(GenProg):
    def __init__(self, ctx, function, holes):
        super(Random, self).__init__()
        self.ctx = ctx
        self.function = function
        self.holes = holes

    def crossover(self):
        pass

    def mutate(self):
        pass

    def evaluate_fitness(self):
        pass

    def run(self):
        population = generatePopulation()
        return population

    def generatePopulation(self):

        population = []

        for i in range(self.POPULATION_SIZE):
            individual_holes = [
                synthesis.se(self.ctx, hole, self.DEPTH) for hole in self.holes
            ]
            individual = self.function.copy()
            individual.replaceHoles(individual, individual_holes)
            population.append(individual)

        return population
