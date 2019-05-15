def wrap_node_t(n):
    return hasattr(n, "type") and n.type or "?"

def prettyprint(n):
    if type(n) == type([]):
        return "\n".join([ prettyprint(a) for a in n ])
    elif type(n) == type((0,0)):
        # TODO: should be arg?
        return "{} : {}".format(n[0], n[1])
    elif n.nodet == 'invocation':
        return "{}({})".format(n.nodes[0], ", ".join(list(map(prettyprint, n.nodes[1]))))
    elif n.nodet in ["&&", "||", "<", "<=", ">", ">=", "==", "!=", "+", "-", "*", "/", "%"]:
        if len(n.nodes) == 2:
            return "({} {} {})".format(prettyprint(n.nodes[0]), n.nodet, prettyprint(n.nodes[1]))
        else:
            return "({} {})".format(n.nodet, prettyprint(n.nodes[0]))
    elif n.nodet == 'literal':
        return str(n.nodes[0])
    elif n.nodet == 'let':
        return "{} = {}".format(n.nodes[0], prettyprint(n.nodes[1]))
    elif n.nodet == 'atom':
        return "{}".format(n.nodes[0])
    elif n.nodet == 'lambda':
        return "({}) -> {}".format(prettyprint(n.nodes[0]), prettyprint(n.nodes[1]))
    elif n.nodet == 'block':
        return "{{ {} }}".format(";\n".join(list(map(prettyprint, n.nodes))))
    elif n.nodet == 'decl':
        return "{} : {} {{ {} }}".format(n.nodes[0], wrap_node_t(n), prettyprint(n.nodes[6]))
    elif n.nodet == 'native':
        return "native {} : {}".format(n.nodes[0], wrap_node_t(n))
    elif n.nodet =='argument':
        if len(n.nodes) > 2 and n.nodes[2]:
            return "{} : {} tracked by {}".format(n.nodes[0], n.nodes[1], n.nodes[2])
        else:
            return "{} : {}".format(n.nodes[0], n.nodes[1])
    elif n.nodet == 'type':
        if len(n.nodes) > 1:
            return "type {} as {}".format(n.nodes[0], n.nodes[1])
        else:
            return "type {}".format(n.nodes[0])
    else:
        print("pretty print 1.0:", n)
        return "<UNKNOWN>"