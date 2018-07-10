def prettyprint(n):
    if type(n) == type([]):
        return "\n".join([ prettyprint(a) for a in n ])
    elif n.nodet == 'invocation':
        return "{}({})".format(n.nodes[0], ", ".join(list(map(prettyprint, n.nodes[1]))))
    elif n.nodet in ["&&", "||", "<", "<=", ">", ">=", "==", "!=", "+", "-", "*", "/", "%"]:
        return "({} {} {})".format(prettyprint(n.nodes[0]), n.nodet, prettyprint(n.nodes[1]))
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
        return "{} : {} {{ {} }}".format(n.nodes[0], n.type, prettyprint(n.nodes[6]))
    elif n.nodet == 'native':
        return "native {} : {}".format(n.nodes[0], n.type)
    elif n.nodet == 'argument':
        if len(n.nodes) > 2:
            return "{} : {} tracked by {}".format(n.nodes[0], n.nodes[1], n.nodes[2])
        else:
            return "{} : {}".format(n.nodes[0], n.nodes[1])
    else:
        print("pretty print new_type:", n)
        return "<UNKNOWN>"