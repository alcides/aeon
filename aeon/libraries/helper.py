import importlib

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
        
        # If it is a function
        if hasattr(function, '__specification__'):
            specification = getattr(function, '__specification__')
            implementation = getattr(function, '__implementation__')
            result[function_name] = (specification, implementation)
            
    return result