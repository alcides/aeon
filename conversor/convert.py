from aeon2.ast import *

import aeon.typestructure
import aeon2.types

def convert(ast):

    ctx = defaultTypes()
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
        # Never happens
        print("Convert: Should never reach here")
        return None
    # Declaracao de funcoes
    # ------------------ Function declaration and its elements -----------------
    elif nodet == "decl":
        # Node attributes
        name = node.nodes[0]
        args = node.nodes[1]
        rType = node.nodes[2]
        kind = node.nodes[3] # unkn1 => ...
        dependentType = node.nodes[4] # where [x > 0]
        unkn3 = node.nodes[5] # TODO: unknown??
        block = node.nodes[6]

        ctx[name] = convert_node(ctx, rType)

        result = "{} : ".format(name)

        # TODO: falta tratar os que tem kinds
        # kind = .............

        for argument in args:
            result = "{}{}".format(result, convert_node(ctx, argument))

        result = "{}{}".format(result, convert_node(ctx, rType))

        # TODO: Falta o tipo dependente
        # dependentType = ..........

        result = "{} = {}".format(result, convert_node(ctx, block))

        return result
    # Tipo de retorno da funcao
    elif nodet == "rtype":
        name = node.nodes[0]
        typee = node.nodes[1]
        result = "{}:{}".format(name, convert_type(ctx, typee))
        return (typee.preconditions and '{{{}}}' or '({})').format(result)
    # Argumentos da funcao
    elif nodet == "argument":
        name = node.nodes[0]
        typee = node.nodes[1]
        result = "{}:{}".format(name, convert_type(ctx, typee))
        result = (typee.preconditions and '{{{}}}' or '({})').format(result)
        ctx[name] = result
        return result + " -> "
    elif nodet == "block":

        result = "{}"

        for instruction in node.nodes[:-1]:
            if instruction.nodet == "let":
                name = instruction.nodes[0]
                assign = convert_node(ctx, instruction.nodes[1])
                typee = convert_type(ctx, instruction.nodes[2])
                strInstr = "(\\{}:{} -> {{}} ({}))".format(name, typee, assign)
            else:
                # TODO: Deal with edge case of literal and atom values
                converted = convert_node(ctx, instruction)
                strInstr = "(\\_:{} -> {{}} ({}))".format(ctx[instruction.nodet], converted)
            result = result.format(strInstr)

        lastInstruction = node.nodes[-1]

        if lastInstruction.nodet == "let":
            name = lastInstruction.nodes[0]
            assign = convert_node(ctx, lastInstruction.nodes[1])
            typee = convert_type(ctx, lastInstruction.nodes[2])
            strInstr = "(\\{}:{} -> {})".format(name, typee, assign)
        else:
            converted = convert_node(ctx, lastInstruction)
            strInstr = "(\\_:{} -> {})".format(ctx[lastInstruction.nodet], converted)
        result = result.format(strInstr)

        return result
    else:
        print("TODO:", nodet, node)

# ------------------------------------------------------------------------------
# ----------------------------------- HELPERS ----------------------------------

def convert_type(ctx, typee):
    result = ""
    # TODO: Check if the others attributes are needed too
    if typee.preconditions:
        result = "{}".format(convert_node(ctx, typee.preconditions[0]))
        for cond in typee.preconditions[1:]:
            result = "{} and {}".format(result, convert_node(ctx, cond))
        result = "{} where {}".format(typee.type, result)
    else:
        result = "{}".format(typee.type)
    return result

def defaultTypes():
    ctx = {}
    ctx['+'] = "Integer"
    ctx['-'] = "Integer"
    ctx['*'] = "Integer"
    ctx['/'] = "Integer"
    ctx['%'] = "Integer"
    ctx['>'] = "Boolean"
    ctx['<'] = "Boolean"
    ctx['>='] = "Boolean"
    ctx['<='] = "Boolean"
    ctx['=='] = "Boolean"
    ctx['!='] = "Boolean"
    ctx['==='] = "Boolean"
    ctx['!=='] = "Boolean"
    ctx['&&'] = "Boolean"
    ctx['||'] = "Boolean"
    return ctx
