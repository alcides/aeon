from .typestructure import *
from .java import initial_table


class TypeChecker(object):
    def __init__(self, table):
        self.table = table
        self.stack = [table, {}]

    def push_frame(self):
        self.stack.append({})

    def pop_frame(self):
        self.stack = self.stack[:-1]

    def find(self, kw):
        for frame in self.stack[::-1]:
            if kw in frame:
                return frame[kw]
        return None

    def typelist(self, ns, *args, **kwargs):
        for n in ns:
            self.typecheck(n, *args, **kwargs)
        return ns

    def typecheck(self, n):
        if type(n) == list:
            return self.typelist(n)
        if type(n) == str:
            print(n, "string invalid")
            return n

        if n.nodet == 'decl':
            n.type = n.nodes[2].nodes[1]

            self.table[n.nodes[0]] = FType(
                    argtypes = [x.nodes[1] for x in  n.nodes[1]],
                    rtype=n.type)
            self.push_frame()
            for arg in n.nodes[1]:
                self.stack[-1][arg.nodes[0]] = arg.nodes[1]
            self.typelist(n.nodes[3]) # Body
            self.pop_frame()

        elif n.nodet == 'invocation':
            self.typelist(n.nodes[1])
            name = n.nodes[0]
            if name not in self.table:
                raise Exception("Unknown function", name)
            args = [ c.type for c in n.nodes[1] ]
            ft = self.table[name]
            if ft.argtypes == args:
                n.type = ft.rtype
            else:
                print(ft.argtypes)
                print(args)
                raise Exception("Unknown arguments for ", name, args)
        elif n.nodet == 'lambda':
            self.typelist(n.nodes[0])
            args = [ c.type for c in n.nodes[0] ]
            self.typecheck(n.nodes[1])
            n.type = FType(
                args,
                n.nodes[1].type
            )
        elif n.nodet == 'atom':
            k = self.find(n.nodes[0])
            if k == None:
                raise Exception("Unknown variable ", k)
            n.type = k
        elif n.nodet == 'let':
            # TODO existing variables
            self.typecheck(n.nodes[1])
            n.type = n.nodes[1].type
            self.stack[-1][n.nodes[0]] = n.type
        elif n.nodet in ["&&", "||"]:
            n.type = t_b
            self.typelist(n.nodes)
            for c in n.nodes:
                if c.type != t_b:
                    raise Exception("{} expected boolean arguments in {}. Got {}.".format(n.nodet, c, c.type))
        elif n.nodet in ["<", "<=", ">", ">=", "==", "!="]:
            n.type = t_b
            self.typelist(n.nodes)
        elif n.nodet in ["+", "-", "*", "/", "%"]:
            self.typelist(n.nodes)
            n.type = t_i if all([ k.type == t_i for k in n.nodes]) else t_f
        elif n.nodet == 'block':
            self.typelist(n.nodes)
            if n.nodes:
                n.type = n.nodes[-1].type
            #for c in n.nodes[:-1]:
            #    if c.nodet != 'invocation' and c.type != t_v:
            #        raise Exception("Expression should be void or an invocation:", c)
        elif n.nodet == 'literal':
            pass # Implemented on the frontend
        else:
            print("not done", n.nodet)
        return n


def typecheck(ast):
    tc = TypeChecker(initial_table)
    return tc.typecheck(ast), tc.table
