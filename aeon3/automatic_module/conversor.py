from aeon3.interpreter import run

from aeon3.types import *
from aeon3.ast import * 

import sys
import csv 

def retrieve_fitness_functions(program):
    result = {}
    for declaration in program.declarations:
        if type(declaration) is Definition:
            result[declaration.name] = generate_fitnesses(declaration)
    return result


def generate_fitnesses(declaration):
    if type(declaration.return_type) is not RefinedType:
        # print("Declaration is not a refined type", declaration)
        return None
    and_expressions = generate_and_expressions(declaration.return_type.cond)
    converted_ands = convert_and_expressions(and_expressions)
    englobed_converted_ands = abstract_and_expressions(declaration, converted_ands)    
    interpreted_ands = interprete_and_expressions(englobed_converted_ands)
    # TODO: DELETE LATER
    ls = []
    for expr, function in zip(converted_ands, interpreted_ands):
        ls.append((expr, function))
    return reversed(ls) 
    # return reversed(interpreted_ands)

# 1 - Generate the abstractions so I can englobe the and expressions
def generate_abstractions(declaration):
    typee = declaration.type
    first_abstraction = Abstraction(typee.arg_name, typee.arg_type, None) # None on purpose
    
    abstraction = first_abstraction
    typee = typee.return_type
    
    while typee != declaration.return_type:
        if not typee.arg_name.name.startswith("_"):
            abstraction.body = Abstraction(typee.arg_name, typee.arg_type, None)
            abstraction = abstraction.body
        typee = typee.return_type
    
    if type(typee) is BasicType:
        pass
    elif type(typee) is AbstractionType:
        abstraction.body = Abstraction(typee.arg_name, typee.arg_type, None)
        abstraction = abstraction.body
    elif type(typee) is RefinedType:
        abstraction.body = Abstraction(typee.name, typee.type, None)
        abstraction = abstraction.body
    else:
        print("Opsie in generate_abstractions", typee, type(typee))
        sys.exit(-1)

    return first_abstraction, abstraction

# 2 - Generate the and expressions for the return type
def generate_and_expressions(condition):
    # I always ensure that condition is an Application
    result = []
    if type(condition.target) is Var:
        if condition.target.name == 'And':
            result.append(condition.argument)
            if type(condition.argument) is Application:    
                result += generate_and_expressions(condition.argument)
            else:
                    result.append(condition.argument)
            return result
        else:
            result.append(condition)
    elif type(condition.target) is Abstraction:
        result += condition
    elif type(condition.target) is Application:
        if type(condition.target.target) is Var:
            if condition.target.target.name == 'And':
                result.append(condition.target.argument)
                if type(condition.argument) is Application:
                    result += generate_and_expressions(condition.argument)
                else:
                    result.append(condition.argument)
                return result
        result.append(condition)
    elif type(condition.target) is TApplication:
        result += generate_and_expressions(condition.target)
    elif type(condition.target) is TAbstraction:
        result += generate_and_expressions(condition.body)

    return result

# 3 - Convert each and expression
def convert_and_expressions(and_expressions):
    result = []
    for and_expr in and_expressions:
        result.append(apply_conversion(and_expr))
    return result

# 3.1 obtains the most left var name of the application
def obtain_application_var(and_expr):
    if type(and_expr) is Literal:
        return None
    elif type(and_expr) is Var:
        return and_expr
    elif type(and_expr) is If:
        return None
    elif type(and_expr) is Abstraction:
        return None
    elif type(and_expr) is TAbstraction:
        return obtain_application_var(and_expr.body)
    elif type(and_expr) is TApplication:
        return obtain_application_var(and_expr.target)
    # Application
    else:
        return obtain_application_var(and_expr.target)

# 3.2 Apply conversion
def apply_conversion(and_expr):
    application_var = obtain_application_var(and_expr)
    if application_var is None:
        return and_expr
    elif application_var.name in ['==']:
        return abs_conversion(and_expr)    
    elif application_var.name in ['!']:
        return boolean_conversion(and_expr)
    elif application_var.name in ['&&']:
        return and_conversion(and_expr)
    elif application_var.name in ['||']:
        return or_conversion(and_expr)
    elif application_var.name in ['-->']:
        return implie_conversion(and_expr)
    elif application_var.name in ['>', '<', '<=', '>=', '!=']:
        return if_conversion(and_expr)
    elif application_var.name == '@evaluate':
        return evaluate_conversion(and_expr)
    else:
        return boolean_conversion(and_expr)

# 3.2.1 abs_conversion
def abs_conversion(and_expr):
    result = Application(Var('-'), and_expr.argument)
    result = Application(result, and_expr.target.argument)
    return Application(Var('abs'), result)

# 3.2.2 if_conversion
def if_conversion(and_expr):
    cond = and_expr
    then = Literal(0, BasicType('Integer'))
    otherwise = abs_conversion(and_expr)
    return If(cond, then, otherwise) 

# 3.2.3 and_conversion
def and_conversion(and_expr):
    cond = and_expr
    then = Literal(0, BasicType('Integer'))
    otherwise_left = apply_conversion(and_expr.argument)
    otherwise.right = apply_conversion(and_expr.target.argument)
    otherwise = Application(Application(Var('+'), otherwise_left), otherwise_right)
    return If(cond, then, otherwise)

# 3.2.4 or_conversion
def or_conversion(and_expr):
    cond = and_expr
    then = Literal(0, BasicType('Integer'))
    otherwise_left = apply_conversion(and_expr.argument)
    otherwise.right = apply_conversion(and_expr.target.argument)
    otherwise = Application(Application(Var('min'), otherwise_left), otherwise_right)
    return If(cond, then, otherwise)

# 3.2.5 implie_conversion
def implie_conversion(and_expr):
    # Translate the --> expression to !a V B
    not_a = Application(Var('!'), and_expr.target.argument)
    return apply_conversion(Application(not_a, and_expr.argument))

# 3.2.6 not_conversion
def boolean_conversion(and_expr):
    cond = and_expr
    then = Literal(0, BasicType('Integer'))
    otherwise = Literal(1, BasicType('Integer'))
    return If(cond, then, otherwise)

# 3.2.7 @evaluate('path')
def evaluate_conversion(and_expr, function):
    path = and_expr.argument.name
    function = run(function)
    with open(path) as csv_file:
        csv_reader = csv.reader(csv_file, delimiter=',')
        for row in csv_reader:
            function_result = 0
            for column in row:
                pass
            function_result = function(param)

# 4 - englobe the expressions in abstractions
def abstract_and_expressions(declaration, converted_ands):
    result = []
    for and_expr in converted_ands:
        abstraction, last_abstraction = generate_abstractions(declaration)
        last_abstraction.body = and_expr
        result.append(abstraction)
    return result

# 5 - Interpret the fitness functions
def interprete_and_expressions(englobed_converted_ands):
    return [run(and_expr) for and_expr in englobed_converted_ands]