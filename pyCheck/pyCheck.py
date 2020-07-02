import importlib

from functools import reduce

from aeon.frontend_core import typee, TypingContext

from aeon.ast import Literal, Application, Abstraction, refined_value
from aeon.types import t_f, t_i, t_b, t_s, AbstractionType, RefinedType

from aeon.interpreter import run

from aeon.synthesis.synthesis import se
from aeon.typechecker.typing import check_type

from aeon.typechecker.substitutions import substitution_expr_in_type

from aeon.automatic.utils.fitness_utils import generate_expressions, convert

ty = typee.parse


def provide(*args, **kwargs):
    def wrapper(function):
        
        function.__pyCheck_arguments__ = args
        function.__pyCheck_return_type__ = kwargs
        function.__pyCheck_repeat__ = 1 if 'repeat' not in kwargs else kwargs['repeat']

        return function

    return wrapper

def runall(path):

    bib = importlib.import_module(path)

    for name in dir(bib):

        function = getattr(bib, name)
        
        if not hasattr(function, '__pyCheck_repeat__'):
            continue
        
        repeat = getattr(function, '__pyCheck_repeat__')
        args = getattr(function, '__pyCheck_arguments__')
        kwargs = getattr(function, '__pyCheck_return_type__')

        failed = list()
        accuracies = list()
        
        # SetUp the refined input generator
        context = setUp()
        typees = [ty(param) for param in args]

        # Obtain the kwargs
        return_type = ty(kwargs['expected'])  
        
        # Generate the fitness function in the 
        fitness_functions = generate_fitnesses(typees, return_type)

        for _ in range(repeat):
            values = [se(context, T, 0).value for T in typees]
            
            # Run the function with the values
            result = function(*values)

            if not assert_restriction(context, values, result, typees, return_type):
                failed.append(values)
            
            # Append the accuracies to the temp
            temp = list()

            for f in fitness_functions:
                for val in values:
                    f = f(val)
                f = f(result)
                temp.append(f)

            accuracies.append(temp)
                
        print_result(repeat, typees, failed, accuracies)

        # TODO: add to global, add runall


# =============================================================================
def print_result(repeat, typees, failed, accuracies):

    v_failed = len(failed)

    accuracy = 0.0

    for acc in accuracies:
        accuracy += sum(acc) / len(acc)
    
    accuracy = len(accuracies) - accuracy
    
    print()
    print('-'*80)

    print("Report:")
    print('Tests passed: {} / {}'.format(repeat - v_failed, repeat))
    print('Function Accuracy: {:.2f}%'.format(accuracy))
    print()
    print("Function failed for the following random generated input tests")

    for vals in failed:
        test = '('
        for T, value in zip(typees, vals):
            test = '{}{} = {}, '.format(test, T.name, value)
        test = test[:-2] + ')'
        print(test)


# =============================================================================
def assert_restriction(ctx, inputs, output, typees, return_type):

        result = 1

        return_value = Literal(output, refined_value(output, get_T(output)))

        for value, typee in zip(inputs, typees):
            name = get_name(typee)
            value = Literal(value, refined_value(value, get_T(value)))
            return_type = substitution_expr_in_type(return_type, value, name)

        try:
            check_type(ctx, return_value, return_type)
            print("SUCCESS: Refined test passed for input values: {}".format(inputs))
        except Exception:
            print("ERROR: Refined test failed for input values: {}".format(inputs))
            result = 0

        return result

def setUp():
    ctx = TypingContext()
    ctx.setup()
    return ctx

def get_name(T):
    if isinstance(T, RefinedType):
        return T.name
    if isinstance(T, AbstractionType):
        return T.arg_name
    return '_'
    
def get_T(value):
    if isinstance(value, float):
        return t_f
    elif isinstance(value, int):
        return t_i
    elif isinstance(value, bool):
        return t_b
    elif isinstance(value, str):
        return t_s
    return None


# =============================================================================
def generate_fitnesses(typees, return_type):

    typees = typees + [return_type]
    typees = reversed(typees)
    and_expressions = generate_expressions(return_type.cond)
    and_expressions = convert(and_expressions)

    result = list()

    for and_expr in and_expressions:
        f = reduce(lambda body, T: Abstraction(T.name, T.type, body), typees, and_expr)
        result.append(run(f))
    
    return result