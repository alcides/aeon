from aeon.frontend.frontend import mk_parser

# Given a file, parses the file and imports the program
def parse(path):
    from aeon.libraries.stdlib import initial_context
    
    text = open(path).read() 

    return mk_parser(path=path, context=initial_context).parse(text)

# Given an expression of a program, parse it and imports it
def parse_strict(text, extra_ctx=dict()):
    return mk_parser(context=extra_ctx).parse(text)
