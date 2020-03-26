from aeon.types import t_f
from aeon.ast import Literal, If

# Given a list of expressions, convert them into numeric discrete values
def convert(and_expressions):
    return [apply_conversion(condition) for condition in and_expressions]

# Apply the conversion to an expression
def apply_conversion(condition):
    then = Literal(0.0, t_f)
    otherwise = Literal(1.0, t_f)
    return If(condition, then, otherwise)
