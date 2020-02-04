from aeon.synthesis import se
from aeon.types import TypingContext, BasicType

from aeon.interpreter import run
from aeon.automatic.utils import replace_holes, generate_abstractions
from aeon.automatic.individual import Individual

from aeon.automatic.operators.evaluate import generate_inputs
from aeon.automatic.operators.initialize import initialize
from aeon.automatic.operators.mutation import mutate
from copy import deepcopy

from aeon.typechecker import check_program

import random

class GenProg(object):

    MAX_DEPTH = 5
    MAX_GENERATIONS = 100
    POPULATION_SIZE = 2

    ELITISM = 1
    NOVELTY = 10
    MUTATION_RATE = 0.1
    CROSSOVER_RATE = 0.8

    AMOUNT_TESTS = 100

    TIMES = 5

    def __init__(self, declaration, holes, eval_ctx, context, fitness_functions):
        self.declaration = declaration
        self.holes = holes
        self.eval_ctx = eval_ctx
        self.type_context = context
        self.fitness_functions = fitness_functions

        self.select = None
        self.evaluate = None
        self.mutate = mutate
        self.crossover = None
        self.initialize = initialize
        
        
    def evaluate_fitness(self, population):

        # The abstractions of the declaration
        abstractions, _ = generate_abstractions(self.declaration)

        # Generate inputs and interpret them
        inputs = generate_inputs(abstractions, self.type_context, self.AMOUNT_TESTS)

        for individual in population:
            
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
        population = self.initialize(self.holes, self.POPULATION_SIZE, self.MAX_DEPTH)
        self.evaluate_fitness(population)

        # print(population)

        # Run every generation until an individual is found
        for _ in range(self.MAX_GENERATIONS):
            '''
            new_population = []
            
            # Select
            new_population = self.select(...)

            for _ in range(self.POPULATION_SIZE):
                # Crossover
                parent1 = select1
                parent2 = select2
                individual = self.crossover(self.type_context, self.MAX_DEPTH, parent1, parent2)
                
                # Mutate
                if random.random() < self.MUTATION_RATE:
                    individual = self.mutate(self.type_context, self.MAX_DEPTH, individual) # TODO: set individual

                new_population.append(individual)
            
            # Evaluate
            self.evaluate_fitness(new_population)
            
            # Sort the individuals
            population = sorted(self.population, key=lambda x : x.fitness)

            population = new_population

            # TODO: nao gosto de breaks, == cuidado, erro virgula
            if population[0].fitness == 0.0:
                break
            '''
            pass
        
        mutation = self.mutate(self.type_context, self.MAX_DEPTH, population[0])
        print(mutation)
        return population[0]