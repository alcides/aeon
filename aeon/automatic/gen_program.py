from aeon.synthesis import se
from aeon.types import TypingContext, BasicType

from aeon.interpreter import run
from aeon.automatic.utils import replace_holes, generate_abstractions
from aeon.automatic.individual import Individual

from aeon.automatic.operators.evaluate import generate_inputs

from copy import deepcopy

from aeon.typechecker import check_program

class GenProg(object):

    MAX_DEPTH = 20
    MAX_GENERATIONS = 100
    POPULATION_SIZE = 10

    ELITISM = 1
    NOVELTY = 10
    MUTATION_RATE = 0.1
    CROSSOVER_RATE = 0.8

    AMOUNT_TESTS = 100

    TIMES = 5
    DEPTH = 5

    def __init__(self, declaration, holes, eval_ctx, context, fitness_functions):
        self.declaration = declaration
        self.holes = holes
        self.eval_ctx = eval_ctx
        self.type_context = context
        self.fitness_functions = fitness_functions

        self.population = list()
        self.select = None
        self.mutate = None
        self.crossover = None
        
    def initialize(self):
        for i in range(self.POPULATION_SIZE):
            synthesized = [se(ctx, hole, self.DEPTH) for ctx, hole in self.holes]
            self.population.append(synthesized)
            print("Generated: ", declaration)
        
    def evaluate_fitness(self):

        # The abstractions of the declaration
        abstractions, _ = generate_abstractions(self.declaration)

        for individual in self.population:
            # 1. Interpret the individual
            interpreted = run(individual.synthesized, self.eval_ctx)

            # 2. Generate inputs and interpret them
            #inputs = generate_inputs(abstractions, self.type_context, self.AMOUNT_TESTS)
            #inputs = []

            # 3. Get the output from running the function
            # 4. Run the fitness functions and obtain results
            pass


    def evolve(self):
        
        # Generate and evaluate the initial population
        self.initialize()
        self.evaluate_fitness()

        # Run every generation until an individual is foudn
        for i in range(self.MAX_GENERATIONS):
            
            # Select

            # Crossover

            # Mutate

            # Evaluate

            pass
