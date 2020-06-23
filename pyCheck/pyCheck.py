from functools import reduce

from aeon.frontend_core import typee, TypingContext

from aeon.ast import Literal, Application, refined_value
from aeon.types import t_f, t_i, t_b, t_s, AbstractionType, RefinedType

from aeon.synthesis.synthesis import se
from aeon.typechecker.typing import check_type

from aeon.typechecker.substitutions import substitution_expr_in_type

ty = typee.parse

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
        

def provide(*args, **kwargs):
    def wrapper(function):
        
        failed = list()
        
        # SetUp the refined input generator
        context = setUp()
        typees = [ty(param) for param in args]

        # Obtain the kwargs
        return_type = ty(kwargs['expected'])
        repeat = 1 if 'repeat' not in kwargs else kwargs['repeat']

        for _ in range(repeat):
            values = [se(context, T, 0).value for T in typees]
            
            # Run the function with the values
            result = function(*values)

            if not assert_restriction(context, values, result, typees, return_type):
                failed.append(values)
                

        print()

        v_failed = len(failed)
        percent_failed = round(v_failed / repeat * 78)
        percent_passed = 78 - percent_failed
        
        print("[{}{}]".format('█' * percent_passed, '-' * percent_failed))

        print("Report:")
        print('Tests passed: {} / {} \n'.format(repeat - v_failed, repeat))
        print("Function failed for the following random generated input tests")

        for vals in failed:
            test = '('
            for T, value in zip(typees, vals):
                test = '{}{} = {}, '.format(test, T.name, value)
            test = test[:-2] + ')'
            print(test)

        return function

    return wrapper