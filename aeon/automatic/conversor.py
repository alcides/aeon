from aeon.interpreter import run
from aeon.automatic.utils import generate_abstractions

from aeon.ast import Var, Literal, Abstraction, Application, If, TAbstraction, TApplication

# Given a list of expressions, convert them into numeric discrete values
def convert(and_expressions):
    return [apply_conversion(condition) for condition in and_expressions]

# Apply the conversion to an expression
def apply_conversion(condition):
    variable = obtain_application_var(condition)
    if isinstance(variable, If):
        variable.then = apply_conversion(variable.then)
        variable.otherwise = apply_conversion(variable.otherwise)
        return condition
    elif isinstance(variable, Abstraction):
        variable.body = apply_conversion(variable.body)
        return condition
    # Else it is a Var
    elif variable.name.startswith('@'):
        return condition
    elif variable.name in ['==']:
        return abs_conversion(condition)
    elif variable.name in ['!']:
        return not_conversion(condition)
    elif variable.name in ['&&']:
        return and_conversion(condition)
    elif variable.name in ['||']:
        return or_conversion(condition)
    elif variable.name in ['-->']:
        return implie_conversion(condition)
    elif variable.name in ['>', '<', '<=', '>=', '!=']:
        return if_conversion(condition)
    # It is a variable or f(variable)
    else:
        return boolean_conversion(condition)

# Obtains the most left var name of the application
def obtain_application_var(condition):
    if isinstance(condition, Var):
        return condition
    elif isinstance(condition, TAbstraction):
        return obtain_application_var(condition.body)
    elif isinstance(condition, TApplication):
        return obtain_application_var(condition.target)
    elif isinstance(condition, Application):
        return obtain_application_var(condition.target)
    # condition is Abstraction or If
    else:
        return condition

# =============================================================================
# ============================================================ Conversion rules
# a == b ~> abs(a - b)
def abs_conversion(condition):
    result = Application(Var('-'), condition.argument)
    result = Application(result, condition.target.argument)
    return Application(Var('abs'), result)

# condition ~> condition ? 0 : abs_conversion(condition)
def if_conversion(condition):
    then = Literal(0, BasicType('Integer'))
    otherwise = abs_conversion(condition)
    return If(condition, then, otherwise)

# a && b ~> a && b ? 0 : convert(a) + convert(b)
def and_conversion(condition):
    then = Literal(0, BasicType('Integer'))
    otherwise_left = apply_conversion(condition.argument)
    otherwise.right = apply_conversion(condition.target.argument)
    otherwise = Application(Application(Var('+'), otherwise_left),
                            otherwise_right)
    return If(condition, then, otherwise)

# a || b ~> a || b ? 0 : min(convert(a), convert(b))
def or_conversion(condition):
    then = Literal(0, BasicType('Integer'))
    otherwise_left = apply_conversion(condition.argument)
    otherwise.right = apply_conversion(condition.target.argument)
    otherwise = Application(Application(Var('min'), otherwise_left),
                            otherwise_right)
    return If(condition, then, otherwise)

# a --> b ~> convert(!a || b)
def implie_conversion(condition):
    not_a = Application(Var('!'), condition.target.argument)
    return apply_conversion(Application(not_a, and_expr.argument))

# !condition ~> revert(condition ? 0 : convert(condition))
def not_conversion(condition):
    converted = apply_conversion(condition.argument)
    # If it is a regular if conversion. Revert everything
    if isinstance(converted, If):
        converted.condition = condition
    else:
        converted = boolean_conversion(condition)
    return converted

# x or f(x) ~> f(x) ? 0 : 1
def boolean_conversion(condition):
    then = Literal(0, BasicType('Integer'))
    otherwise = Literal(1, BasicType('Integer'))
    return If(cond, then, otherwise)

# =============================================================================
# ================================================ Fitness functions conversion
def interpret_expressions(abstractions, expressions):

    abstraction, last_abstraction = abstractions

    optimizers = {'@maximize': maximize, 
                  '@minimize': minimize, 
                  '@evaluate': evaluate}

    result = list()
    
    for condition in expressions:
        if isinstance(condition, Application) and \
                isinstance(condition.target, Var) and \
                condition.target.name.startswith('@'):
            function = optimizers[condition.target.name]
            result.append(function(condition.argument.name))
        else:
            # Englobe the expressions with the parameters and return
            last_abstraction = condition
            function = run(abstraction)
            result.append(function)

    return result

# @maximize
def maximize():
    pass

# @minimze
def minimize():
    pass

# @evaluate('path')
def evaluate(path):
    # Applies a function to a row and get its error
    def apply(function, row):
        return abs(row[-1] - reduce(lambda f, x: f(x), row[:-1], function))

    with open(path) as csv_file:
        csv_reader = csv.reader(csv_file, delimiter=',')
        return lambda f: sum([apply(f, row) for row in csv_reader[1:]])
    
    raise Exception('The csv file', path, 'is invalid.')
