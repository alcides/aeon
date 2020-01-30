from aeon.synthesis import se
from aeon.interpreter import run

def generate_inputs(abstraction, context, size_tests):

    result = list()

    for i in range(size_tests):
        current = abstraction

        inputs = []

        while current.body != None:
            print(current)
            typee = abstraction.arg_type
            inputs.append(se(context, typee, 3))
            current = current.body

        print("INPUTS:", inputs)
        result.append(tuple(inputs))
    return result

