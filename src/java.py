from .typestructure import *

initial_table = {
    'J.iif': Type(arguments=[t_b, Type(arguments=[], type=t_i), Type(arguments=[], type=t_i)], type=t_i),
    'J.out': Type(arguments=[t_i], type=t_i),
    'J.timeit': Type(arguments=[Type(arguments=[], type=t_i)], type=t_i),
    'F.future': Type(arguments=[Type(arguments=[], type=t_i)], type=Type("aeminium.runtime.futures.Future", parameters=[t_i])),
    'F.get': Type(arguments=[Type("aeminium.runtime.futures.Future", parameters=[t_i])], type=t_i),
}

def type_convert(t):
    if t.type == 'Array':
        return t.parameters[0] + "[]"
    if t.type == 'Void':
        return 'void'
    return str(t)
