from aeon.types import t_i, t_f
from aeon.ast import Var, Literal, Hole, Abstraction, Application, If, TAbstraction, TApplication

# Given a list of expressions, convert them into numeric discrete values
def convert(and_expressions):
    return [apply_conversion(condition) for condition in and_expressions]

# Apply the conversion to an expression
def apply_conversion(condition):

    variable = obtain_application_var(condition)
    
    if isinstance(variable, Literal):
        return boolean_conversion(condition)
    
    elif isinstance(variable, Var):
        return boolean_conversion(condition)
    
    elif isinstance(variable, Hole):
        return condition # Never happens

    elif isinstance(variable, If):
        variable.then = apply_conversion(variable.then)
        variable.otherwise = apply_conversion(variable.otherwise)
        return condition
    
    elif isinstance(variable, Abstraction):
        variable.body = apply_conversion(variable.body)
        return condition

    # Else it is surely a Var
    elif variable.name.startswith('@'):
        return condition
    elif variable.name == '==':
        return abs_conversion(condition)
    elif variable.name == '!=':
        return neg_abs_conversion(condition)
    elif variable.name == '!':
        return not_conversion(condition)
    elif variable.name == '&&':
        return and_conversion(condition)
    elif variable.name == '||':
        return or_conversion(condition)
    elif variable.name == '-->':
        return implie_conversion(condition)
    elif variable.name == '>':
        return greater_than_conversion(condition)
    elif variable.name == '<':
        return less_than_conversion(condition)
    elif variable.name == '<=':
        return less_or_equal_conversion(condition)
    elif variable.name == '>=':
        return greater_or_equal_conversion(condition)
    # It is the application of a function
    else:
        return boolean_conversion(condition)

# Obtains the most left var name of the application
def obtain_application_var(condition):
    
    if isinstance(condition, Literal):
        return condition

    elif isinstance(condition, Var):
        return condition

    elif isinstance(condition, Hole):
        return condition

    elif isinstance(condition, If):
        return condition
    
    elif isinstance(condition, Abstraction):
        return condition

    elif isinstance(condition, Application):
        return obtain_application_var(condition.target)
    
    elif isinstance(condition, TAbstraction):
        return obtain_application_var(condition.body)
    
    elif isinstance(condition, TApplication):
        return obtain_application_var(condition.target)
    
    else:
        raise Exception("Unknown node while obtaining application", condition)


# =============================================================================
# ============================================================ Conversion rules
# a == b ~> norm(|a - b|) 
def abs_conversion(condition):
    result = Application(Var('-'), condition.target.argument)
    result = Application(result, condition.argument)
    result = Application(Var('abs'), result)
    return normalize(result)


# a != b ~> 1 - norm(|a - b|)
def neg_abs_conversion(condition):
    converted = abs_conversion(condition)
    return Application(Application(Var('-'), Literal(1.0, t_f)), converted)


# condition ~> condition ? 0 : abs_conversion(condition)
def if_conversion(condition):
    then = Literal(0.0, t_f)
    otherwise = abs_conversion(condition)
    return If(condition, then, otherwise)


# a > b ~> norm(relu(y - x + offset))
def greater_than_conversion(condition):
    result = Application(Var('-'), condition.argument)
    result = Application(result, condition.target.argument)
    result = Application(Application(Var('+'), result), Literal(1.0, t_f))
    return normalize(relu(result))

# a < b ~> norm(relu(x - y + offset))
def less_than_conversion(condition):
    result = Application(Var('-'), condition.target.argument)
    result = Application(result, condition.argument)
    result = Application(Application(Var('+'), result), Literal(1.0, t_f))
    return normalize(relu(result))


# a >= b ~> norm(relu(y - x))
def greater_or_equal_conversion(condition):
    result = Application(Var('-'), condition.argument)
    result = Application(result, condition.target.argument)
    return normalize(relu(result))


# a <= b ~> norm(relu(x - y))
def less_or_equal_conversion(conditon):
    result = Application(Var('-'), condition.target.argument)
    result = Application(result, condition.argument)
    return normalize(relu(result))

# a && b ~> (convert(a) + convert(b)) / 2
def and_conversion(condition):
    left = apply_conversion(condition.argument)
    right = apply_conversion(condition.target.argument)
    op = Application(Application(Var('+'), left), right)
    return Application(Application(Var('/'), op), Literal(2, t_i))


# a || b ~> min(f(a), f(b))
def or_conversion(condition):
    left = apply_conversion(condition.argument)
    right = apply_conversion(condition.target.argument)
    return Application(Application(Var('min'), left), right)


# a --> b ~> convert(!a || b)
def implie_conversion(condition):
    not_a = Application(Var('!'), condition.target.argument)
    expression = Application(Application(Var('||'), not_a), condition.argument)
    return apply_conversion(expression)


# !condition ~> 1 - convert(condition)
def not_conversion(condition):
    converted = apply_conversion(condition.argument)
    return Application(Application(Var('-'), Literal(1.0, t_f)), converted)


# x, f(x) ~> f(x) ? 0 : 1
def boolean_conversion(condition):
    then = Literal(0.0, t_f)
    otherwise = Literal(1.0, t_f)
    return If(condition, then, otherwise)


# ========================================== Auxiliary functions for conversion
# normalize
def normalize(value):
    norm = Application(Application(Var('pow'), Literal(0.99, t_f)), value)
    return Application(Application(Var('-'), Literal(1.0, t_f)), norm)

# ReLU
def relu(condition):
    return Application(Application(Var('max'), Literal(0.0, t_f)), condition)
