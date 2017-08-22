from .typestructure import *

initial_table = {
    'J.iif': FType([t_b, FType([], t_i), FType([], t_i)], t_i),
    'J.out': FType([t_i], t_v),
}

def type_convert(t):
    if t.t == 'Array':
        return t.tpars[0] + "[]"
    if t.t == 'Void':
        return 'void'
    return str(t)