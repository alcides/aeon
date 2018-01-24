def prettyprint(n):
    if n.nodet == 'invocation':
        return "{}({})".format(n.nodes[0], ", ".join(list(map(prettyprint, n.nodes[1:]))))
    elif n.nodet in ["&&", "||", "<", "<=", ">", ">=", "==", "!=", "+", "-", "*", "/", "%"]:
        return "({} {} {})".format(prettyprint(n.nodes[0]), n.nodet, prettyprint(n.nodes[1]))
    elif n.nodet == 'literal':
        return n.nodes[0]
    elif n.nodet == 'let':
        return "{} = {}".format(n.nodes[0], prettyprint(n.nodes[1]))
    elif n.nodet == 'atom':
        return "{}".format(n.nodes[0])
    elif n.nodet == 'lambda':
        return "({}) -> {}".format(prettyprint(n.nodes[0]), prettyprint(n.nodes[1]))
    elif n.nodet == 'block':
        return "{{ {} }}".format(";\n".join(list(map(prettyprint, n.nodes))))
    else:
        print("pretty print new_type:", n)
        return "<UNKNOWN>"