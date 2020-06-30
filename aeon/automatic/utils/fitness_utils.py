from aeon.ast import Literal, Var, Hole, If, Application, Abstraction, TAbstraction, TApplication
from aeon.types import BasicType, AbstractionType, RefinedType, TypeAbstraction, TypeApplication

from aeon.automatic.evaluation.conversor import convert, obtain_application_var

from aeon.interpreter import run
from aeon.synthesis.synthesis import se_safe

from aeon.typechecker.substitutions import substitution_expr_in_expr

import timeit

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
        and_expressions = filter_typees(definition.return_type.name, and_expressions)
        
        # 3. Convert each expression
        and_expressions = convert(and_expressions)

        # 4. Translate the ast into fitness functions
        fitness_functions = interpret_expressions(eval_ctx, definition, and_expressions)

    return fitness_functions


# =============================================================================
# Obtain the types of the input parameters
def generate_typees(declaration):
    
    result = list()

    typee = declaration.type

    while typee != declaration.return_type:
        result.append(typee.arg_type)
        typee = typee.return_type

    return result


# =============================================================================
# Generates random inputs for the functions
def generate_inputs(typees, context, eval_ctx, size):
    
    result = list()

    for _ in range(size):
        # Synthesize leafs only trees
        inputs = [run(se_safe(context, typee, 0), eval_ctx) for typee in typees]
        result.append(inputs)

    return result


# =============================================================================
# Obtain a list of and expressions from a condition
def generate_expressions(condition):
    
    result = list()

    # If it is an expression (('And' condition) condition)
    if isinstance(condition, Application) and \
        isinstance(condition.target, Application) and \
        isinstance(condition.target.target, Var) and \
        condition.target.target.name == 'And':

        result += generate_expressions(condition.argument)
        result += generate_expressions(condition.target.argument)

    else:
        result.append(condition)

    return result


# =============================================================================
# Filter the restrict types from the and expressions
def filter_typees(output_name, expressions):

    def is_dependent(node):
            
        if isinstance(node, Literal):
            return False
            
        elif isinstance(node, Var):
            import aeon.libraries.stdlib as stdlib
            return not stdlib.is_builtin(node.name) and node.name != output_name
        
        elif isinstance(node, Hole):
            return False
        
        elif isinstance(node, If):
            return is_dependent(node.cond) or \
                   is_dependent(node.then) or \
                   is_dependent(node.otherwise)
        
        elif isinstance(node, Application):
            return is_dependent(node.target) or \
                   is_dependent(node.argument)
        
        elif isinstance(node, Abstraction):
            return is_dependent(node.body)
        
        elif isinstance(node, TAbstraction):
            return is_dependent(node.body)
        
        elif isinstance(node, TApplication):
            return is_dependent(node.target)
        
        else:
            raise Exception("Unable to filter the node:", node)
    
    return [condition for condition in expressions if is_dependent(condition)]


# =============================================================================
# Obtain the interpreted fitness functions from the and expressions
def interpret_expressions(eval_ctx, definition, expressions):

    optimizers = {
        '@maximize': lambda x: maximize(eval_ctx, definition, x),
        '@minimize': lambda x: minimize(eval_ctx, definition, x),
        '@evaluate': lambda x: evaluate(eval_ctx, definition, x),
        'forall': lambda x: forall(eval_ctx, definition, x),
        'exists': lambda x: exists(eval_ctx, definition, x),
    }

    result = list()
    
    for condition in expressions:

        name = obtain_application_var(condition)

        # If it is one of the optimizers functions
        if isinstance(name, Var) and name.name in optimizers:
            function = optimizers[name.name]
            result.append(function(condition))

        # If it is a regular function
        else:
            function = generate_fitness(eval_ctx, definition, condition)            
        
        result.append(function)

    return result


def generate_fitness(eval_ctx, definition, condition):
    # Get function parameters
    abstraction, last_abstraction = generate_abstractions(definition) 

    # Englobe the expressions with the parameters and return
    last_abstraction.body = condition

    return run(abstraction, eval_ctx)


# Generate the abstractions so they englobe the and expressions
def generate_abstractions(definition):
   
    typee = definition.type
    
    first_abstraction = Abstraction(typee.arg_name, typee.arg_type, None)
    abstraction = first_abstraction
    
    typee = typee.return_type

    # Add the parameters
    while typee != definition.return_type:
        abstraction.body = Abstraction(typee.arg_name, typee.arg_type, None)
        abstraction = abstraction.body
        typee = typee.return_type

    # Add the return type to the abstractions
    if isinstance(typee, BasicType):
        arg_name = '_'
        arg_type = typee

    elif isinstance(typee, AbstractionType):
        arg_name = typee.arg_name
        arg_type = typee.arg_type 
        
    elif isinstance(typee, RefinedType):
        arg_name = typee.name
        arg_type = typee.type
    
    elif isinstance(typee, TypeAbstraction):
        arg_name = '_'
        arg_type = typee
    
    elif isinstance(typee, TypeApplication):
        arg_name = '_'
        arg_type = typee

    else:
        raise Exception("Unknown type when generating abstractions", type)

    # The last abstraaction
    abstraction.body = Abstraction(arg_name, arg_type, None)
    abstraction = abstraction.body

    return first_abstraction, abstraction


# ----------------------------------------------------------- Special functions
# @maximize
def maximize(eval_ctx, definition, condition):
    argument = Application(Application(Var('-'), Literal(1.0, t_f)), condition.argument)
    return generate_fitness(eval_ctx, definition, argument)

# @minimze
def minimize(eval_ctx, definition, condition):
    return generate_fitness(eval_ctx, definition, condition.argument)

# @evaluate('path')
def evaluate(eval_ctx, definition, condition):
    path = condition.argument.name

    # Gaussian normalization of a value between 0.0 and 1.0
    def normalize(value):
        return 1.0 - pow(0.99, value)

    # Applies a function to a row and get its error
    def apply(function, row):
        return normalize(abs(row[-1] - reduce(lambda f, x: f(x), row[:-1], function)))

    with open(path) as csv_file:
        csv_reader = csv.reader(csv_file, delimiter=',')
        return lambda f: sum([apply(f, row) for row in csv_reader[1:]])

    raise Exception('The csv file', path, 'is invalid.')

# forall
def forall(eval_ctx, definition, condition):
    definition.name = '_forall_fitness'
    condition = substitution_expr_in_expr(condition, Var('_forall_fitness'), 'forall')
    return generate_fitness(eval_ctx, definition, condition)
    
# exists
def exists(eval_ctx, definition, condition):
    definition.name = '_exists_fitness'
    condition = substitution_expr_in_expr(condition, Var('_exists_fitness'), 'forall')
    return generate_fitness(eval_ctx, definition, condition)
    