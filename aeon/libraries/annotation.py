def aedocumentation(text):
    def documentation(f):
        f.__documentation__ = text
        return f
    return documentation

def aefunction(spec, implementation):
    def typee(f):
        f.__specification__ = spec
        f.__implementation__ = implementation
        return f
    return typee