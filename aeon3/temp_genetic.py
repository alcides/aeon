from aeon3.interpreter import run

from aeon3.types import *
from aeon3.ast import * 

import sys

class Genetic(object):
    pass


def retrieve_fitness_functions(program):
    result = {}
    for declaration in program.declarations:
        if type(declaration) is Definition:
            result[declaration.name] = generate_fitnesses(declaration)
    print("RESULTADO:", (result['funcao9'][1])(0)(0)(True))
    return result

def has_hole(node):
    if type(node) is Hole:
        return True
    elif type(node) is Literal:
        return False
    elif type(node) is Var:
        return False
    elif type(node) is If:
        return has_hole(node.cond) or has_hole(node.then) or has_hole(node.otherwise)
    elif type(node) is Application:
        return has_hole(node.target) or has_hole(node.argument)
    elif type(node) is Abstraction:
        return has_hole(node.body)
    elif type(node) is TAbstraction:
        return has_hole(node.body)
    elif type(node) is TApplication:
        return has_hole(node.target)
    else:
        return False

def generate_fitnesses(declaration):
    if type(declaration.return_type) is not RefinedType:
        print("Declaration is not a refined type", declaration)
        return None
    and_expressions = generate_and_expressions(declaration.return_type.cond)
    #print("And expressions:")
    #for and_exp in and_expressions:
    #    print(and_exp)
    converted_ands = convert_and_expressions(and_expressions)
    #print("\nConverted And expressions:")
    #for and_exp in converted_ands:
    #    print(and_exp)
    englobed_converted_ands = abstract_and_expressions(declaration, converted_ands)
    #print("\nEnglobed And expressions:")
    #for and_exp in englobed_converted_ands:
    #    print(and_exp)
    
    interpreted_ands = interprete_and_expressions(englobed_converted_ands)
    return interpreted_ands

# 1 - Generate the abstractions so I can englobe the And expressions
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

# 2 - Generate the And expressions for the return type
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

# 3 - Convert each And expression
def convert_and_expressions(and_expressions):
    pass
    result = []
    for and_expr in and_expressions:
        application_var = obtain_application_var(and_expr)
        if application_var is None:
            result.append(and_expr)
        elif application_var.name in ['==']:
            result.append(abs_conversion(and_expr))
        elif application_var.name in ['&&', '||', '-->', '!']:
            # TODO:
            print("TODO: ", application_var.name)
            result.append(and_expr)
            pass
        elif application_var.name in ['>', '<', '<=', '>=', '!=']:
            result.append(if_conversion(and_expr))
        else:
            result.append(and_expr)
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
    
# 3.2 abs_conversion
def abs_conversion(and_expr):
    result = Application('-', and_expr.argument)
    result = Application(result, and_expr.target.argument)
    return Application('abs', result)

# 3.2 if_conversion
def if_conversion(and_expr):
    cond = and_expr
    then = Literal(0, BasicType('Integer'))
    otherwise = abs_conversion(and_expr)
    return If(cond, then, otherwise) 

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