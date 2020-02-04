from aeon.synthesis import se_safe
from aeon.interpreter import run

def generate_inputs(abstraction, context, size_tests):

    result = list()

    for i in range(size_tests):
        inputs = []
        current = abstraction

        while current.body != None:
            typee = current.arg_type
            inputs.append(se_safe(context, typee, 0).value)
            current = current.body
            
        result.append(tuple(inputs))

    return result

