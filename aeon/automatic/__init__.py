from aeon.automatic import Genetics

from aeon.automatic.fitness.conversor import convert

from aeon.automatic.utils.tree_utils import replace_holes
from aeon.automatic.utils.utils import build_evaluation_context, add_evaluation_context
from aeon.automatic.utils.fitness_utils import generate_expressions, filter_typees, interpret_expressions

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


# =============================================================================
# Auxiliary: Given a definition, generate its fitness functions
def generate_fitness_functions(eval_ctx, definition):

    fitness_functions = list()

    # Check if there are conditions for the fitness function
    if isinstance(definition.return_type, RefinedType):

        # 0. Obtain the condition from the return type
        conditions = definition.return_type.cond
        
        # 1. Get each 'And' expression
        and_expressions = generate_expressions(conditions)

        # 2. Filter expressions to obtain the dependent types only
        and_expressions = filter_typees(and_expressions)

        # 3. Convert each expression
        and_expressions = convert(and_expressions)

        # 4. Translate the ast into fitness functions
        fitness_functions = interpret_expressions(eval_ctx, definition, and_expressions)

    return fitness_functions