import copy
import signal

from functools import reduce

from aeon.interpreter import run
from aeon.automatic.utils.tree_utils import replace_holes
from aeon.automatic.utils.fitness_utils import generate_inputs, generate_typees

from aeon.automatic.parameters import TESTS_SIZE, MAX_FITNESS

def evaluate(population, genetics):

    # Copy of the contexts
    typing_context = genetics.type_context.copy()
    evaluation_context = genetics.eval_ctx.copy()

    # Remove the program that we are trying to generate
    del typing_context.variables[genetics.declaration.name]

    # Obtain the types of the arguments 
    argument_typees = generate_typees(genetics.declaration)

    # Generate inputs for the program
    tests = generate_inputs(argument_typees, typing_context, evaluation_context, TESTS_SIZE)

    for individual in population:

        # Fill the holes of the declaration
        declaration = genetics.declaration.copy()
        synthesized = replace_holes(declaration, individual.synthesized.copy())

        # Interpret the individual
        interpreted = run(synthesized, evaluation_context)

        # For each fitness function, run the randomly generated tests
        fitness_arguments = list()

        # Obtain the value of running the program    
        for test in tests:   
            result = run_test(test, interpreted)
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

# =============================================================================
# Auxiliary function
def run_test(test, interpreted):
    
    try:        
        result = reduce(lambda f, x: f(x), test, interpreted)
    except Exception:
        print("Function exceeded time...")
        result = MAX_FITNESS

    return result
