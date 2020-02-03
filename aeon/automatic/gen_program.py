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
    POPULATION_SIZE = 2

    ELITISM = 1
    NOVELTY = 10
    MUTATION_RATE = 0.1
    CROSSOVER_RATE = 0.8

    AMOUNT_TESTS = 10

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
            expression = [se(ctx, hole, self.DEPTH) for ctx, hole in self.holes]
            self.population.append(Individual(expression))
        
    def evaluate_fitness(self):

        # The abstractions of the declaration
        abstractions, _ = generate_abstractions(self.declaration)

        for individual in self.population:
            
            # Generate inputs and interpret them
            inputs = generate_inputs(abstractions, self.type_context, self.AMOUNT_TESTS)
       
            # Fill the holes and interpret the individual
            synthesized = deepcopy(self.declaration)
            replace_holes(synthesized, deepcopy(individual.synthesized))

            # Interpret the individual
            interpreted = run(synthesized, self.eval_ctx)
            
            # Get the output from running the function
            tests = []
            for function_input in inputs:
                res = interpreted
                for param in function_input:
                    res = res(param)
                tests.append(function_input + (res,))

            # Codigo feio, depois melhoro
            # Run the fitness functions and obtain results
            individual_fitness = list()
            for fitness in self.fitness_functions:
                total = 0
                for test in tests:
                    result = fitness
                    for param in test:
                        result = result(param)
                    total += result
                individual_fitness.append(total)
            
            # Add the fitness to the individual
            individual.add_fitness(individual_fitness)


    def evolve(self):
        
        # Generate and evaluate the initial population
        self.initialize()
        self.evaluate_fitness()

        print(self.population)

        # Run every generation until an individual is foudn
        for i in range(self.MAX_GENERATIONS):
            
            # Select

            # Crossover

            # Mutate

            # Evaluate

            pass
