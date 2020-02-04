from typing import List, Tuple

from aeon.automatic.gen_program import GenProg

from aeon.ast import Definition, Program
from aeon.types import TypingContext, Type, RefinedType

from aeon.interpreter import run, EvaluationContext

from aeon.automatic.conversor import convert
from aeon.automatic.conversor import interpret_expressions

from aeon.automatic.utils import has_holes, generate_expressions, generate_abstractions, filter_dependent_types

from aeon.types import TypingContext, BasicType


# Returns the definition with its holes filled
# holed : List[Tuple[Definition, List[Tuple[TypingContext, Type]]]]
def automatic(program: Program, context: TypingContext, holed):

    # 1. Build the context for the fitness functions
    eval_ctx = build_evaluation_context(program)

    for declaration, holes in holed:

        # 2. Get the fitness functions
        fitness_functions = generate_fitness_functions(eval_ctx, declaration)

        # 3. Prepare the evolution
        genetic = GenProg(declaration, holes, eval_ctx, context, fitness_functions)

        # 4. Run the genetic approach and get generated expressions
        synthesized_individual = genetic.evolve()

        # 5. Fill the holes with the synthesized individual 
        # function = 

        # 6. Now that the hole has been filled, run, so it is available to add to ctx
        # run(function, eval_ctx)

    return program

# Builds the evaluation context with unholed functions for fitness functions
def build_evaluation_context(program: Program):
    eval_ctx = EvaluationContext()
    unholed_program = []

    for declaration in program.declarations:
        if not has_holes(declaration):
            if isinstance(declaration, Definition) and declaration.name != 'main':
                run(declaration, eval_ctx)

    return eval_ctx

# Given a definition, generate its fitness functions
def generate_fitness_functions(eval_ctx: EvaluationContext, definition: Definition):

    fitness_functions = []

    # Check if there are conditions for the fitness function
    if isinstance(definition.return_type, RefinedType):

        # 0. Obtain the condition from the return type
        conditions = definition.return_type.cond
        
        # 1. Get each 'And' expression
        and_expressions = generate_expressions(conditions)

        # 2. Filter expressions to obtain the dependent types only
        and_expressions = filter_dependent_types(eval_ctx, and_expressions)

        # 3. Convert each expression
        and_expressions = convert(and_expressions)

        # 4. Translate the ast into fitness functions
        fitness_functions = interpret_expressions(eval_ctx, definition, and_expressions)

    return fitness_functions
