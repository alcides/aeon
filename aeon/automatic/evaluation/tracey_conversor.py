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
    elif variable.name == 'forall':
        return forall_conversion(condition)
    elif variable.name == 'exists': 
        return exists_conversion(condition)
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
global K
K = 5

# a == b ~> if |a - b| == 0 then 0 else |a - b| + K
def abs_conversion(condition):
    result = mk_bin_op('-', condition.target.argument, condition.argument)
    result = mk_un_op('abs', result)

    zero = Literal(0, t_i)
    condition = mk_bin_op('==', result, zero)

    return if_result(condition, zero, result)


# a != b ~> if |a - b| != 0 then 0 else (0 + K)
def neg_abs_conversion(condition):
    
    zero = Literal(0, t_i)

    result = mk_bin_op('-', condition.target.argument, condition.argument)
    result = mk_un_op('abs', result)
    condition = mk_bin_op('!=', result, zero)

    return if_result(condition, zero, zero)


# a < b ~> if a - b < 0 then 0 else (a - b) + K
def less_than_conversion(condition):

    zero = Literal(0, t_i)

    result = mk_bin_op('-', condition.target.argument, condition.argument)
    condition = mk_bin_op('==', result, zero)
    
    return if_result(condition, zero, result)


# a <= b ~> if a - b < 0 then 0 else (a - b) + K
def less_or_equal_conversion(conditon):
   
    zero = Literal(0, t_i)

    result = mk_bin_op('-', condition.target.argument, condition.argument)
    condition = mk_bin_op('==', result, zero)
    
    return if_result(condition, zero, result)


# a > b ~> convert(b < a)
def greater_than_conversion(condition):
    left = condition.target.argument
    right = condition.argument

    condition.argument = left
    condition.target.argument = right

    condition.target.target.target.name = '<'

    return less_than_conversion(condition)
    

# a >= b ~> convert(b <= a)
def greater_or_equal_conversion(condition):
    left = condition.target.argument
    right = condition.argument

    condition.argument = left
    condition.target.argument = right

    condition.target.target.target.name = '<='

    return less_or_equal_conversion(condition)

# a && b ~> convert(a) + convert(b)
def and_conversion(condition):
    left = apply_conversion(condition.argument)
    right = apply_conversion(condition.target.argument)
    return mk_bin_op('+', left, right) 


# a || b ~> min(f(a), f(b))
def or_conversion(condition):
    left = apply_conversion(condition.argument)
    right = apply_conversion(condition.target.argument)
    return mk_bin_op('min', left, right)


# a --> b ~> min(!a, b)
def implie_conversion(condition):
    not_left = mk_un_op('!', condition.target.argument)
    right = condition.argument

    not_left = apply_conversion(not_left)
    right = apply_conversion(condition.argument)

    return mk_bin_op('min', not_left, right)


# ∀ x ∈ X : Q : W   ~> if X : Q is empty then 0 else ...
def forall_conversion(condition):
    raise NotImplementedError("To be implemented")


# ∃ x ∈ X : Q : W   ~> if X : Q is empty then K else ...
def exists_conversion(condition):    
    raise NotImplementedError("To be implemented")


# !condition ~> 1 - convert(condition)
def not_conversion(condition):
    raise NotImplementedError("To be implemented")


# x, f(x) ~> f(x) ? 0 : K
def boolean_conversion(condition):
    zero = Literal(0, t_i)
    return if_result(condition, zero, zero)


# ========================================== Auxiliary functions for conversion
def if_result(condition, then, otherwise):
    otherwise = Application(Application(Var('+'), otherwise), Literal(K, t_i))
    return If(condition, then, otherwise)

def mk_un_op(op, arg):
    return Application(Var(op), arg)

def mk_bin_op(op, left, right):
    return Application(Application(Var(op), left), right)