import importlib
import aeon3.frontend

# Returns a dict with the function implementations {name: function, ...}
def importNative(path, function_name):
    result = {}
    bib = importlib.import_module(path)    
    # Imports everything
    if function_name == '*':
        for name in dir(bib):
            if not name.startswith('_'):
                result = {**result, **importNative(path, name)}
    else:
        function = getattr(bib, function_name)
        result[function_name] = function
    return result