# type: ignore[no-redef]

from aeon.ast import *
from aeon.types import *

from aeon.libraries.stdlib import is_builtin

from multipledispatch import dispatch

tab_size = 0
buffer = dict()

# ======================================================== Abstract Syntax Tree
@dispatch(Program)
def translate(node):

    result = ''
    
    for declaration in node.declarations:
        tab_size = 0
        translated = translate(declaration)
        if len(translated) > 0:
            result = '{}{}\r\n\r\n'.format(result, translated)
    
    buffer = get_buffer()

    for key, value in buffer.items():
        if value:
            temp = ''
            for x in value:
                temp = '{}{};\r\n'.format(tab(), x)
            result = 'type {} {{\r\n{}}}\r\n\r\n{}'.format(key, temp, result)
        else:
            result = 'type {};\r\n\r\n{}'.format(key, result)

    return result

''' [Typee] '''
@dispatch(Hole)
def translate(node):
    return '[{}]'.format('' if node.type is bottom else translate(node.type))

''' true | false | 0 | 0.0 '''
@dispatch(Literal)
def translate(node):
    if isinstance(node.value, str):
        return "\"" + node.value + "\""

    return str(node.value)

''' x '''
@dispatch(Var)
def translate(node):
    return node.name

''' if expr {statement} else {statement} | expr ? expr : expr '''
@dispatch(If)
def translate(node):

    result = ''

    if is_statement(node.then) or is_statement(node.otherwise):
        raise_tab()
        result = 'if {} {{\r\n{};\r\n{}}} else {{\r\n{};\r\n{}}};'.format('{}', '{}', tab(), {}, tab())

    else:
        result = '{} ? {} : {};'

    cond = translate(node.cond)
    then = translate(node.then)
    other = translate(node.otherwise)

    return result.format(cond, then, other)

''' x + y, -x, !x, f(x) '''
@dispatch(Application)
def translate(node):

    # If it is the Application(Abstraction(_, ..., body), argument)
    if is_statement(node):
        statements = translate(node.target.body)
        expression = translate(node.argument)
        return '{};\r\n{}{}'.format(expression, tab(), statements)

    else:
        is_native = lambda node, lista: (isinstance(node.target, Application) and \
                                        isinstance(node.target.target, TApplication) and \
                                        isinstance(node.target.target.target, Var) and \
                                        node.target.target.target.name in lista)

        if is_native(node, [
                '+', '-', '*', '/', '%', '^', '>', '<', '>=', '<=', '==',
                '!=', '&&', '||', '-->'
        ]):
            return '{} {} {}'.format(
                translate(node.target.argument),
                translate(node.target.target.target),
                translate(node.argument))
        elif isinstance(node.target, Application) and \
             isinstance(node.target.target, Var) and \
             node.target.target.name in ['&&', '||', '-->']:
             
            return '{} {} {}'.format(
                translate(node.target.argument),
                translate(node.target.target),
                translate(node.argument))

        elif is_native(node, ['!']):
            return '!{}'.format(translate(node.argument))
        
        else:
            arguments = '' if type(
                node.argument) is Var and node.argument.name.startswith(
                    '_') else translate(node.argument)
            tempNode = node.target
            while isinstance(tempNode, Application):
                arguments = '{}, {}'.format(
                    translate(tempNode.argument), arguments)
                tempNode = tempNode.target
            return '{}({})'.format(translate(tempNode), arguments)

''' \\x:Typee -> expr '''
@dispatch(Abstraction)
def translate(node):
    arg_name = node.arg_name
    typee = translate(node.arg_type)
    expression = translate(node.body)
    return '\{}:{} -> {}'.format(arg_name, typee, expression)
    

''' expr<T> '''
@dispatch(TAbstraction)
def translate(node):
    return '{}<{}>'.format(translate(node.body), translate(node.type))


''' expr<Typee> '''
@dispatch(TApplication)
def translate(node):
    return '{}<{}>'.format(translate(node.target), translate(node.argument))


''' name(param) -> out {statements} '''
@dispatch(Definition)
def translate(node):

    # Get the abstractions of the function
    abstractions = ''
    tempTypee = node.type

    while isinstance(tempTypee, TypeAbstraction):
        abstractions = '{}, {}'.format(abstractions,
                                        translate(tempTypee.name))
        tempTypee = tempTypee.type
    abstractions = '<' + abstractions[2:] + '>' if len(
        abstractions) > 0 else abstractions

    # Get the typee
    typee = '{}:{}'.format(tempTypee.arg_name,
                            translate(tempTypee.arg_type))
    tempTypee = tempTypee.return_type
    while tempTypee != node.return_type:
        typee = '{}, {}:{}'.format(typee, tempTypee.arg_name,
                                    translate(tempTypee.arg_type))
        tempTypee = tempTypee.return_type

    # Get the return type
    return_type = translate(node.return_type)

    if isinstance(node.body, Var) and node.body.name == 'native':
        return '{}{} : ({}) -> {} = {};'.format(node.name, abstractions,
                                                typee, return_type,
                                                translate(node.body))
    
    elif isinstance(node.body, Var) and node.body.name == 'uninterpreted':
        # splitted[0] has type name, splitted[1] has ghost variable name
        splitted = node.name.split('_')[1:]
        result = '{}:{}'.format(splitted[1], return_type)
        get_buffer_value(splitted[0]).append(result)
        return ''
    
    else:
        raise_tab()
        tempBody = node.body
        while isinstance(tempBody,
                            Abstraction) or type(tempBody) is TAbstraction:
            tempBody = tempBody.body
        return '{}{} : ({}) -> {} {{\r\n{}{};\r\n}}'.format(
            node.name, abstractions, typee, return_type, tab(),
            translate(tempBody))

@dispatch(TypeDeclaration)
def translate(node):
    add_buffer(node.name, list())
    return ""
    
@dispatch(TypeAlias)
def translate(node):
    return 'type {} as {};'.format(node.name, translate(node.type))

# ======================================================================= Types 
@dispatch(BasicType)
def translate(node):
    return str(node)

@dispatch(AbstractionType)
def translate(node):
    return '(\{}:{} -> {})'.format(node.arg_name, translate(node.arg_type),
                                    translate(node.return_type))

@dispatch(RefinedType)
def translate(node):
    return '{{{}:{} | {}}}'.format(node.name, translate(node.type),
                                    translate(node.cond))

@dispatch(TypeAbstraction)
def translate(node):
    return '{}<{}>'.format(translate(node.type), node.name)

@dispatch(TypeApplication)
def translate(node):
    return '{}<{}>'.format(translate(node.target),
                            translate(node.argument))

@dispatch(object)
def translate(node):
    raise Exception('Unknown node during translation:', type(node), node)

# =================================================================== Auxiliary
def raise_tab():
    global tab_size
    tab_size += 1

def decrease_tab():
    global tab_size
    tab_size -= 1

def tab():
    global tab_size
    return '\t' * tab_size

def add_buffer(key, value):
    global buffer
    buffer[key] = value

def get_buffer():
    global buffer
    return buffer

def get_buffer_value(key):
    global buffer
    return buffer[key]

def is_statement(node):
    return isinstance(node, Application) and \
            isinstance(node.target, Abstraction)
