import importlib
from functools import reduce

import aeon3.frontend


def aetype(str):
    def typee(f):
        f.__aetype__ = str
        return f

    return typee


# Returns a dict with the function implementations {name: (specification, function), ...}
def importNative(path, function_name):
    result = {}
    bib = importlib.import_module(path)
    # Imports everything
    if function_name == '*':
        for name in dir(bib):
            result = {**result, **importNative(path, name)}
    else:
        function = getattr(bib, function_name)
        if hasattr(function, '__aetype__'):
            typee = getattr(function, '__aetype__')
            result[function_name] = (typee, function)
    return result
