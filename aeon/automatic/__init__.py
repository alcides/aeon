import logging

from aeon.automatic.automatic import Genetics

from aeon.automatic.utils.tree_utils import replace_holes
from aeon.automatic.utils.fitness_utils import generate_fitness_functions
from aeon.automatic.utils.utils import build_evaluation_context, add_evaluation_context, preprocess_holed


def automatic(program, context, holed):

    holed = preprocess_holed(holed)

    logging.info("Building the evaluation context...")

    # Build the context for the fitness functions
    eval_ctx = build_evaluation_context(program)

    for declaration, holes in holed:

        logging.info(f"Synthesising the declaration: {declaration}")

        # Get the fitness functions
        fitness_functions = generate_fitness_functions(eval_ctx, declaration)

        logging.info(
            f"Evaluating with the fitness functions: {fitness_functions}")

        # Prepare the evolution
        genetics = Genetics(declaration, holes, eval_ctx, context,
                            fitness_functions)

        # Run the genetic approach and get generated expressions
        individual = genetics.evolve()

        logging.info(f"Generated the individual: {individual}")

        # Fill the holes with the synthesized individual
        declaration = replace_holes(declaration, individual.synthesized)

        logging.info(f"Declaration synthesised: {declaration}")

        # Now that the hole has been filled, run, so it is available to add to ctx
        add_evaluation_context(declaration, eval_ctx)

    return program
