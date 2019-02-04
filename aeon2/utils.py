from .ast import *

def orNone(existing, fnew):
    if existing == None:
        return None
    else:
        return fnew(existing)


def merge_nones(a, b):
    if a == None:
        return b
    elif b == None:
        return a
    else:
        return a + b
        
        
def replace_vars(n, mapping):
    if type(n) is Atom:
        if n.name in mapping.keys():
            n.name = mapping[n.name]
    elif type(n) is Literal:
        pass
    elif type(n) is Operator:
        replace_vars(n.arguments[0], mapping)
        if len(n.arguments) > 1:
            replace_vars(n.arguments[1], mapping)
    elif type(n) is Invocation:
        for a in n.arguments:
            replace_vars(a, mapping)
    else:
        print("TODO: replace vars in", n)
    return n