from inspect import signature

def aedocumentation(text):
    def documentation(f):
        f.__documentation__ = text
        return f
    return documentation

def aefunction(spec):
    def typee(f):
        f.__specification__ = spec
        amount = len(signature(f).parameters)
        f.__implementation__ = create_function(f, amount, list())
        return f
    return typee

def create_function(function, amount, acc):
    if amount == 0:
        return function(*acc)
    return lambda x: create_function(function, amount - 1, acc + [x])