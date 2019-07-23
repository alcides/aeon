from aeon2.ast import *

import aeon.typestructure
import aeon2.types

def convert(ast):

    ctx = defaultTypes()
    converted = []

    for node in ast:
        print("=" * 30)
        converted.append(convert_node(ctx, node)[1])

    return converted


def convert_node(ctx, node):

    nodet = node.nodet

    print(node)

    # Literal
    if nodet == 'literal':
        return node.type, node.nodes[0]

    # Variavel
    elif nodet == 'atom':
        return ctx[node.nodes[0]], node.nodes[0]

    # Invocacao de uma funcao
    elif nodet == 'invocation':
        result = "{}".format(node.nodes[0])
        for argument in node.nodes[1]:
            _, converted = convert_node(ctx, argument)
            result = "({}({}))".format(result, converted)
        return ctx[node.nodes[0]], result

    # Funcao nativa
    elif nodet == 'native':
        # Node attributes
        name = node.nodes[0]
        args = node.nodes[1]
        rType = node.nodes[2]
        kind = node.nodes[3] # T => ...
        dependentType = node.nodes[4] # where [x > 0]
        unkn3 = node.nodes[5] # TODO: unknown??

        ctx[name], _ = convert_node(ctx, rType)

        result = "{} : ".format(name)

        # TODO: falta tratar os que tem kinds
        # kind = .............

        for argument in args:
            result = "{}{}".format(result, convert_node(ctx, argument)[1])

        result = "{}{} = native;".format(result, convert_node(ctx, rType)[1])

        # TODO: Falta o tipo dependente
        # dependentType = ..........
        
        return rType, result

    # Operacoes nativas
    elif nodet in ['+', '-', '*', '/', '%', '>', '<', '<=', '>=',
                   '==', '!=', '===', '&&', '||' '!==']:
        arguments = node.nodes
        _, arg1 = convert_node(ctx, arguments[0])
        _, arg2 = convert_node(ctx, arguments[1])
        result ="({} {} {})".format(arg1, nodet, arg2)
        return nodet, result

    # Declaracao de uma variavel
    elif nodet == 'let':
        name = node.nodes[0]
        _, expression = convert_node(ctx, node.nodes[1])
        typee = convert_type(ctx, node.nodes[2])

        ctx[name] = typee

        return typee, expression

    # Declaracao de funcoes
    # ------------------ Function declaration and its elements -----------------
    elif nodet == "decl":
        # Node attributes
        name = node.nodes[0]
        args = node.nodes[1]
        rType = node.nodes[2]
        kind = node.nodes[3] # T => ...
        dependentType = node.nodes[4] # where [x > 0]
        unkn3 = node.nodes[5] # TODO: unknown??
        block = node.nodes[6]

        ctx[name], _ = convert_node(ctx, rType)

        result = "{} : ".format(name)

        # TODO: falta tratar os que tem kinds
        # kind = .............

        for argument in args:
            result = "{}{}".format(result, convert_node(ctx, argument)[1])

        result = "{}{}".format(result, convert_node(ctx, rType)[1])

        # TODO: Falta o tipo dependente
        # dependentType = ..........

        block.type = ctx[name] # small hack

        result = "{} = {}".format(result, convert_node(ctx, block)[1])

        return ctx[name], result

    # Tipo de retorno da funcao
    elif nodet == "rtype":
        name = node.nodes[0]
        typee = convert_type(ctx, node.nodes[1])
        result = "{}:{}".format(name, typee)
        return typee, (node.nodes[1].preconditions and '{{{}}}' or '({})').format(result)

    # Argumentos da funcao
    elif nodet == "argument":
        name = node.nodes[0]
        ctx[name] = None
        typee = convert_type(ctx, node.nodes[1])
        result = "{}:{}".format(name, typee)
        result = (node.nodes[1].preconditions and '{{{}}}' or '({})').format(result)
        ctx[name] = typee
        return typee, result + " -> "

    # Bloco de instrucoes do metodo
    elif nodet == "block":

        result = '{}'

        i = 0

        for instruction in node.nodes[:-1]:
            typee, representation = convert_node(ctx, instruction)
            var = instruction.nodet == 'let' and instruction.nodes[0] or '_'

            # TODO: Nao gosto muito disto, alterar mais tarde
            if i == 0:
                typee = node.type
                i += 1

            strInstr = "(\\{}:{} -> {{}} ({}));".format(var, typee, representation)
            result = result.format(strInstr)

        lastInstruction = node.nodes[-1]

        typee, representation = convert_node(ctx, lastInstruction)
        var = lastInstruction.nodet == 'let' and lastInstruction.nodes[0] or '_'
        strInstr = "(\\{}:{} -> {});".format(var, typee, representation)
        result = result.format(strInstr)

        return typee, result
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
    ctx['out'] = "Object" # TODO: temp
    return ctx
