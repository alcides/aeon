from aeon2.ast import *

import aeon.typestructure
import aeon2.types

def convert(ast):
    converted = []

    for node in ast:
        print("=" * 30)
        print(node)
        converted.append(convert_node(node))

    result = Program(converted)
    print("Resultado: ", result)
    return result


def convert_node(node):

    print(node, type(node))

    nodet = node.nodet
    # literal ~> Literal()
    if nodet == "literal":
        # Literal()
        nLiteral = node.nodes[0]
        nType = None
        return Literal(nLiteral, nType)
    # atom ~> Var()
    elif nodet == "atom":
        # Var()
        return Var(node.nodes[0])
    elif nodet == "rtype":

        varName = node.nodes[0]
        varType = node.nodes[1]

        typee = aeon2.types.BasicType(str(varType.type))

        result = typee

        # TODO: I predict a bug somewhere here
        if varType.preconditions:
            cond = convert_node(varType.preconditions[0])
            result = aeon2.types.RefinedType(varName, typee, cond)

        return result
    elif nodet == 'invocation':
        function_name = node.nodes[0]
        # TODO: What happens to functions which can have multiple arguments?
    # native operation ~> Application()
    elif nodet in ['+', '-', '*', '/', '%', '>', '<', '<=', '>=', '==', '!=', '===', '&&', '||' '!==']:
        arguments = node.nodes
        if len(arguments) > 1:
            argument = convert_node(node.nodes[-1])
            node.nodes = node.nodes[0:-1]
            target = convert_node(node)
        else:
            argument = convert_node(arguments[0])
            target = Var(nodet)
        return Application(target, argument)
    # declaration ~> definition
    elif nodet == "decl":
        nName = node.nodes[0]  # String
        nType = convert_node(node.nodes[2])
        nBody = convert_node(node.nodes[-1])  #
        return Definition(nName, nType, nBody)
    elif nodet == "block":
        program = []
        for son in node.nodes:
            print("="*20, "\n","Doing", son)
            program.append(convert_node(son))

        print("RES:")
        for asd in program:
            print(asd, type(asd))
        return program
    else:
        print("TODO:", node.nodet, node)
