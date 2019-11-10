from typing import List, Tuple

from aeon.ast import Definition
from aeon.types import TypingContext, Type

from aeon.automatic.conversor import convert
from aeon.automatic.conversor import interprete_expressions

from aeon.automatic.utils import generate_expressions

# Returns the definition with its holes filled
def generate(definition: Definition, holes: List[Tuple[TypingContext, Type]]):

    # Get the fitness functions
    fitness_functions = generate_fitness_functions(definition)

    # Choose a genetic approach 
    genetic_approach = Random(definition, fitness_functions, holes)
    
    # Run the genetic approach and get filled program
    generated = genetic_approach.run()

    return generated

# Given a definition, generate its fitness functions
def generate_fitness_function(definition: Definition):

    # It must be a RefinedType, otherwise we aren't able to generate
    conditions = definition.return_type.cond

    # 1. Get each 'And' expression
    and_expressions = generate_expressions(conditions)
    
    # 2. Get function parameters
    abstractions = generate_abstractions(definition)

    # 3. Convert each expression
    and_expressions = convert(and_expressions)

    # 4. Translate the ast into fitness functions
    fitness_functions = interprete_expressions(abstractions, and_expressions)

    return fitness_functions