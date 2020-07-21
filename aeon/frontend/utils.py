from aeon.ast import *
from aeon.types import *

from functools import reduce

# =============================================================================
# Removes every single TypeAbstraction and returns the type
def remove_tabs(typee):
    if isinstance(typee, BasicType):
        return typee
    elif isinstance(typee, RefinedType):
        typee.type = remove_tabs(typee.type)
    elif isinstance(typee, AbstractionType):
        typee.arg_type = remove_tabs(typee.arg_type)
        typee.return_type = remove_tabs(typee.return_type)
    elif isinstance(typee, TypeApplication):
        typee.target = remove_tabs(typee.target)
        typee.argument = remove_tabs(typee.argument)
    elif isinstance(typee, TypeAbstraction):
        typee = remove_tabs(typee.type)
    return typee

# Remove the inner tabs that are in the tabs
def remove_inner_tabs(typee, tabs):
    def remotion(tee, curr_tabs):
        if isinstance(tee, BasicType):
            return tee
        elif isinstance(tee, RefinedType):
            tee.type = remotion(tee.type, curr_tabs)
        elif isinstance(tee, AbstractionType):
            tee.arg_type = remotion(tee.arg_type, curr_tabs)
            tee.return_type = remotion(tee.return_type, curr_tabs)
        elif isinstance(tee, TypeApplication):
            tee.target = remotion(tee.target, curr_tabs)
            tee.argument = remotion(tee.argument, curr_tabs)
        elif isinstance(tee, TypeAbstraction):
            if tee.name == curr_tabs:
                tee = remotion(tee.type, curr_tabs)
            else:
                tee.type = remotion(tee.type, curr_tabs)
        return tee
    
    for curr_tabs in tabs:
        typee = remotion(typee, curr_tabs)
        
    return typee

# Removes internal TAbstractions and puts them outside
def process_tabs(typee):
    tabs = search_tabs(typee)
    typee = remove_tabs(typee)
    typee = englobe_typeabs(typee, reversed(tabs))
    return typee

# Search for abstractions in a given type and return the list of them: [X, Y]
def search_tabs(typee):
    abstractions = []

    # Check if the BasicType is a TypeeIdentifier
    if isinstance(typee, BasicType):
        if len(typee.name) == 1:
            abstractions = [typee.name]
    
    # Check the RefinedType type
    elif isinstance(typee, RefinedType):
        abstractions = search_tabs(typee.type)
    
    # Check the AbstractionType arg_type and return_type
    elif isinstance(typee, AbstractionType):
        arg_type = search_tabs(typee.arg_type)
        return_type = search_tabs(typee.return_type)
        abstractions = arg_type + return_type
    
    # Check the TypeApplication target and argument
    elif isinstance(typee, TypeApplication):
        target = search_tabs(typee.target)
        argument = search_tabs(typee.argument)
        abstractions = target + argument
    
    # Check the name of each TypeAbstraction, progress the typee and return it
    elif isinstance(typee, TypeAbstraction):
        while isinstance(typee, TypeAbstraction):
            abstractions = abstractions + search_tabs(
                typee.name)
            typee = typee.type
        abstractions = abstractions + search_tabs(typee)
    
    return (list(dict.fromkeys(abstractions)))

# Englobe the typee in the tabstractions
def englobe_typeabs(ttype, tabs):
    return reduce(lambda abst, retType: TypeAbstraction(retType, star, abst),
            tabs, ttype)

def englobe_typeapps(ttype, tapps):
    return reduce(lambda target, argument: TypeApplication(target, argument),
            tapps, ttype)

# =============================================================================
# Given a type obtain its type name
def get_type_name(typee : Type):
    if isinstance(typee, BasicType):
        return typee.name
    elif isinstance(typee, RefinedType):
        return get_type_name(typee.type)
    elif isinstance(typee, AbstractionType):
        return get_type_name(typee.return_type)
    elif isinstance(typee, TypeApplication):
        return get_type_name(typee.target)
    elif isinstance(typee, TypeAbstraction):
        return get_type_name(typee.type)
    else:
        raise Exception("Unknown type when obtaining the basic type name")

def get_type_kind(typee : Type):
    if isinstance(typee, BasicType):
        return star
    elif isinstance(typee, RefinedType):
        return star
    elif isinstance(typee, AbstractionType):
        return star
    elif isinstance(typee, TypeApplication):
        return Kind(star, get_type_kind(typee.target))
    elif isinstance(typee, TypeAbstraction):
        return get_type_kind(typee.type)
    else:
        raise Exception("Unknown type when obtaining the kind:", type(typee))

# =============================================================================
# Given the arguments of a definition, preprocess it
def preprocess_native(args):
    
    name = args.pop(0).value
    (tabs, tapps), params = (list(), list()), list()

    if isinstance(args[0], tuple):
        (tabs, tapps) = args.pop(0)
    
    if isinstance(args[0], list):
        params = args.pop(0)
    
    ttype = args.pop(0)

    return name, (tabs, tapps), params, remove_tabs(ttype)

def preprocess_regular(args):

    name = args.pop(0).value
    (tabs, tapps), params, body = (list(), list()), list(), None

    if isinstance(args[0], tuple):
        (tabs, tapps) = args.pop(0)

    if isinstance(args[0], list) and isinstance(args[0][0], tuple):
        params = args.pop(0)
    
    ttype = args.pop(0)

    body = convert_body(args)

    return name, (tabs, tapps), params, remove_tabs(ttype), body

def convert_body(statements):
    statements.reverse()
    node = statements[0]

    if isinstance(node, Definition):
        node = Application(Abstraction(node.name, node.type, Var(node.name)) , node.body)

    for statement in statements[1:]:
        if isinstance(statement, Definition):
            name, typee, body = statement.name, statement.type, statement.body
        else:
            name, typee, body = '_', top, statement

        # Create the abstraction and application
        node = Application(Abstraction(name, typee, node), body)

    return node
    
def create_definition_ttype(params, rtype):
    params = reversed(params)
    return reduce(lambda ttype, p: AbstractionType(p[0], p[1], ttype),
            params, rtype)

# =============================================================================
# Generates the uninterpreted function from a name.ghost
def generate_uninterpreted(ctx, attributes):

    # Variable, its type and the ghost attributes over the variable
    variable = attributes[0]
    typee = ctx[variable]

    attributes = attributes[1:]

    target_name = f'{get_type_name(typee)}_{attributes[0]}'
    
    target = Var(target_name)

    result = Application(wrap_tapplications(target, remove_tabs(typee)), Var(variable))

    # Progress the attributes variable
    for attr in attributes[1:]:
        ttype = get_type_name(ctx[target_name])
        result = Application(Var(f'{ttype}_{attr}'), result) 

    return result

def wrap_tapplications(target, typee):
    while isinstance(typee, TypeApplication):
        target = TApplication(target, typee.argument)
        typee = typee.target
    return target
    
# =============================================================================
# Resolve the imports
def resolve_imports(path, program):
    result = []
    from ..libraries.stdlib import add_function
    for node in program:
        if isinstance(node, Import):
            # Get the os path for the ae file

            importPath = node.name
            absolutePath = os.path.normpath(
                os.path.join(os.getcwd(), os.path.dirname(path), importPath))
            realPath = absolutePath + ".ae"

            # It is a regular .ae import
            if os.path.exists(realPath):
                importedProgram = parse(realPath)
                # If we only want a specific function from the program
                if node.function is not None:
                    importedProgram.declarations = list(filter(lambda x : isinstance(x, Definition) \
                                                and x.name == node.function, \
                                                importedProgram.declarations))
            # It is a .py import
            else:
                moduleName = node.name.replace("/", ".")
                importedProgram = Program([])
                natives = importNative(
                    moduleName,
                    '*' if node.function is None else node.function)
                for native in natives.keys():
                    aetype_code, function = natives[native]

                    imported_declarations = parse_strict(
                        aetype_code).declarations
                    aetype = imported_declarations[0]  # Fixed
                    if isinstance(aetype, Definition):
                        add_function(aetype.name, aetype.type, function)
                    importedProgram.declarations.append(aetype)
                    importedProgram.declarations.extend(
                        imported_declarations[1:])
            result = result + importedProgram.declarations
        else:
            result.append(node)
    return result