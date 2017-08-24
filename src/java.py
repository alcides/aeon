from .typestructure import *

initial_table = {
    'J.iif': FType([t_b, FType([], t_i), FType([], t_i)], t_i),
    'J.out': FType([t_i], t_v),
    'F.future': FType([FType([], t_i)], Type("aeminium.runtime.futures.Future", [t_i])),
    'F.get': FType([Type("aeminium.runtime.futures.Future", [t_i])], t_i),
}

def type_convert(t):
    if t.t == 'Array':
        return t.tpars[0] + "[]"
    if t.t == 'Void':
        return 'void'
    return str(t)
