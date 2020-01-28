from aeon.synthesis import se
from aeon.types import TypingContext, BasicType

from aeon.automatic.individual import Individual

class GenProg(object):

    MAX_DEPTH = 20
    MAX_GENERATIONS = 100
    POPULATION_SIZE = 100

    ELITISM = 1
    NOVELTY = 10
    MUTATION_RATE = 0.1
    CROSSOVER_RATE = 0.8

    TIMES = 5
    DEPTH = 5

    def __init__(self, declaration, holes, eval_ctx, fitness_functions):
        self.declaration = declaration
        self.holes = holes
        self.eval_ctx = eval_ctx
        self.fitness_functions = fitness_functions

        self.population = list()
        self.select = None
        self.crossover = None
        self.mutate = None
        
    def initialize(self):
        
        for i in range(self.POPULATION_SIZE):
            print(">"*10, "Generating individual", i)
            synthesized = [se(ctx, hole, self.DEPTH) for ctx, hole in self.holes]
            print(synthesized)
            # Add the individual to the population
            self.population.append(Individual(synthesized))
        
    def evaluate_fitness(self):
        pass

    def evolve(self):
        
        # Generate and evaluate the initial population
        self.population = self.initialize()
        self.evaluate_fitness()

        # Run every generation until an individual is foudn
        for i in range(self.MAX_GENERATIONS):
            
            # Select

            # Crossover

            # Mutate

            # Evaluate

            pass
