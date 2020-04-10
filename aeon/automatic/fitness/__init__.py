import copy

from functools import reduce

from aeon.interpreter import run
from aeon.automatic.utils.tree_utils import replace_holes
from aeon.automatic.utils.fitness_utils import generate_inputs, generate_typees

from aeon.automatic.parameters import TESTS_SIZE

def evaluate(population, genetics):

    # Obtain the types of the arguments 
    argument_typees = generate_typees(genetics.declaration)

    # Generate inputs for the program
    tests = generate_inputs(argument_typees, genetics.type_context, TESTS_SIZE)

    for individual in population:

        # Fill the holes of the declaration
        declaration = genetics.declaration.copy()
        synthesized = replace_holes(declaration, individual.synthesized.copy())
        
        # Interpret the individual
        interpreted = run(synthesized, genetics.eval_ctx)
        
        # For each fitness function, run the randomly generated tests
        fitness_arguments = list()

        # Obtain the value of running the program    
        for test in tests:
            # TODO: Make it stop after 5: mandar fork and kill
            # https://stackoverflow.com/questions/492519/timeout-on-a-function-call
            # https://pypi.org/project/func-timeout/
            # https://pypi.org/project/timeout-decorator/

            result = reduce(lambda f, x: f(x), test, interpreted)
            fitness_arguments.append(test + [result])

        # Run the fitness functions and obtain fitness
        for fitness in genetics.fitness_functions:

            total = 0.0

            # For each test, apply the fitness function
            for test in fitness_arguments:
                result = reduce(lambda f, x: f(x), test, fitness)
                total += result
            
            # Add the fitness result to the individual 
            individual.add_fitness(total)

    return population