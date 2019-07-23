from aeon2.ast import *

import aeon.typestructure
import aeon2.types

def convert(ast):

    ctx = {}
    converted = []

    for node in ast:
        print("=" * 30)
        converted.append(convert_node(ctx, node))

    result = converted
    print("Resultado: ", result)
    return result


def convert_node(ctx, node):

    print(node, type(node))

    nodet = node.nodet

    # Literal ou variavel
    if nodet in ['literal', 'atom']:
        return node.nodes[0]

    # Invocacao de uma funcao
    elif nodet == 'invocation':
        result = "{}".format(node.nodes[0])
        for argument in node.nodes[1]:
            result = "({}({}))".format(result, convert_node(ctx, argument))
        return result
    # Operacoes nativas
    elif nodet in ['+', '-', '*', '/', '%', '>', '<', '<=', '>=',
                   '==', '!=', '===', '&&', '||' '!==']:
        arguments = node.nodes
        arg1 = convert_node(ctx, arguments[0])
        arg2 = convert_node(ctx, arguments[1])
        result ="({} {} {})".format(arg1, nodet, arg2)
        return result
    # Declaracao de uma variavel
    elif nodet == 'let':
        print("TODO: LET")
        return None
    # Declaracao de funcoes
    # ------------------ Function declaration and its elements -----------------
    elif nodet == "decl":
        # TODO:
        nName = node.nodes[0] # str
        arguments = []
        for arg in node.nodes[1]:
            arguments.append(convert_node(ctx, arg))
        nType = convert_node(ctx, node.nodes[2])
        nBody = convert_node(ctx, node.nodes[-1])

        ctx[nName] = nType
        return Definition(nName, nType, nBody)
    # Tipo de retorno da funcao
    elif nodet == "rtype":
        name = node.nodes[0]
        typee = node.nodes[1]
        result = convert_type(ctx, name, typee)
        return (typee.preconditions and '{{{}}}' or '({})').format(result)
    elif nodet == "argument":
        # TODO:
        print("\n>>>>>>>> ARGUMENT: ", node, "\n\n")
        return None
    elif nodet == "block":

        result = ""

        for instruction in node.nodes:
            convert_node(ctx, instruction)
            result = "\\x{} -> ".format("ola")

        return result
    else:
        print("TODO:", nodet, node)

# ------------------------------------------------------------------------------
# ----------------------------------- HELPERS ----------------------------------

def convert_type(ctx, name, typee):
    result = ""
    # TODO: Check if the others attributes are needed too
    if typee.preconditions:
        result = "{}".format(convert_node(ctx, typee.preconditions[0]))
        for cond in typee.preconditions[1:]:
            result = "{} and {}".format(result, convert_node(ctx, cond))
        result = "{}:{} where {}".format(name, typee.type, result)
    else:
        result = "{}:{}".format(name, typee.type)
    return result
