from aeon.automatic.automatic import Genetics

from aeon.automatic.utils.tree_utils import replace_holes
from aeon.automatic.utils.fitness_utils import generate_fitness_functions
from aeon.automatic.utils.utils import build_evaluation_context, add_evaluation_context

def automatic(program, context, holed):

    # Build the context for the fitness functions
    eval_ctx = build_evaluation_context(program)

    for declaration, holes in holed:
        
        # Get the fitness functions
        fitness_functions = generate_fitness_functions(eval_ctx, declaration)
        
        # Prepare the evolution
        genetics = Genetics(declaration, holes, eval_ctx, context, fitness_functions)

        # Run the genetic approach and get generated expressions
        individual = genetics.evolve()

        # Fill the holes with the synthesized individual 
        declaration = replace_holes(declaration, individual.synthesized)

        # Now that the hole has been filled, run, so it is available to add to ctx
        add_evaluation_context(declaration, eval_ctx)

    return program
