def translate_h(n):
    if n.nodet == 'atom':
        if n.nodes[0].startswith('self'):
            return True, lambda args: args[0]
        elif n.nodes[0].startswith('__return_'):
            return True, lambda args: args[0]
        elif n.nodes[0].startswith('__argument_'):
            i = int(n.nodes[0].split("_")[-1])
            return True, lambda args: args[1 + i]
        else:
            print("unknown atom in z3 conversion", n.nodes[0])
            return False, None
    elif n.nodet == 'literal':
        return True, lambda args: int(n.nodes[0])
    elif n.nodet in ['<=', '<', '>', '<=', '>=', '==', '+', '-', '*', '/']:
        a_ok, a_l = translate_h(n.nodes[0])
        b_ok, b_l = translate_h(n.nodes[1])
        if (not a_ok) or (not b_ok):
            return False, None
        if n.nodet == '<=':
            return True, lambda args: a_l(args) <= b_l(args)
        elif n.nodet == '<':
            return True, lambda args: a_l(args) < b_l(args)
        elif n.nodet == '>=':
            return True, lambda args: a_l(args) >= b_l(args)
        elif n.nodet == '>':
            return True, lambda args: a_l(args) > b_l(args)
        elif n.nodet == '==':
            return True, lambda args: a_l(args) == b_l(args)
        elif n.nodet == '+':
            return True, lambda args: a_l(args) + b_l(args)
        elif n.nodet == '-':
            return True, lambda args: a_l(args) + b_l(args)
        elif n.nodet == '*':
            return True, lambda args: a_l(args) + b_l(args)
        elif n.nodet == '/':
            return True, lambda args: a_l(args) + b_l(args)
    # TODO: other nodes
    print("unknown node in Z3 conversion!!!!", n)
    return False, None

def translate(predicates):
    z3_predicates = []
    for p in predicates:
        ok, cond_l = translate_h(p)
        if ok:
            z3_predicates.append(cond_l)
    return z3_predicates
