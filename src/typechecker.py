from .typestructure import *


class TypeContext(object):
    def __init__(self, typedecl=None):
        self.types = typedecl and typedecl or []
        self.type_aliases = {}
        self.subclasses = []

        self.types.append(Type('Integer'))
        self.types.append(Type('Boolean'))
        self.types.append(Type('Double'))
        self.types.append(Type('String'))

    def add_type(self, t):
        self.types.append(t)

    def add_type_alias(self, t1, t2):
        self.type_aliases[t1] = t2


class Context(object):
    def __init__(self, tcontext):
        self.stack = []
        self.typecontext = tcontext
        self.push_frame()

    def push_frame(self):
        self.stack.append({})

    def push_frame(self):
        self.stack.append({})

    def pop_frame(self):
        self.stack = self.stack[:-1]

    def find(self, kw):
        for frame in self.stack[::-1]:
            if kw in frame:
                return frame[kw]
        return None

    def set(self, k, v):
        self.stack[-1][k] = v

def is_subtype(a, b, tcontext):
    if b == 'Void':
        return True
    return a == b

def check_function_arguments(args, ft, tcontext):
    if ft.freevars:
        for v in ft.freevars:
            for ct in tcontext.types:
                ft_concrete = ft.copy_replacing_freevar(v, ct)
                a, ft_concrete_r = check_function_arguments(args, ft_concrete, tcontext)
                if a:
                    return (a, ft_concrete_r)
        return (False, None)
    else:
        valid = all([ is_subtype(a, b, tcontext) for a,b in zip(args, ft.arguments) ])
        return (valid, ft)

class TypeChecker(object):
    def __init__(self):
        self.typecontext = TypeContext()
        self.context = Context(self.typecontext)


    def type_error(self, string):
        raise Exception("Type Error", string)

    def is_subtype(self, a, b):
        return is_subtype(a, b, self.typecontext)

    def typelist(self, ns, *args, **kwargs):
        for n in ns:
            self.typecheck(n, *args, **kwargs)
        return ns

    def t_type(self, n):
        self.typecontext.add_type(n.nodes[0])
        if len(n.nodes) > 1:
            self.typecontext.add_type_alias(n.nodes[1], n.nodes[0])

    def t_native(self, n):
        name = n.nodes[0]
        n.type = n.nodes[2].nodes[1]
        ft = Type(arguments = [x.nodes[1] for x in  n.nodes[1]],
                  type=n.type,
                  freevars = n.nodes[4])
        self.context.set(name, ft)

    def t_decl(self, n):
        n.type = n.nodes[2].nodes[1]
        name = n.nodes[0]
        print(name, n.nodes[4])
        ft = Type(arguments = [x.nodes[1] for x in  n.nodes[1]],
                  type=n.type,
                  freevars = n.nodes[4])

        self.context.set(name, ft)

        # Body
        self.context.push_frame()
        for arg in n.nodes[1]:
            self.context.set(arg.nodes[0], arg.nodes[1])
        self.typecheck(n.nodes[3])
        if n.nodes[3]:
            real_type = n.nodes[3].type
        else:
            real_type = t_v

        self.context.pop_frame()
        if not self.is_subtype(real_type, n.type):
            self.type_error("Function {} expected {} and body returns {}".format(name, n.type, real_type))

    def t_invocation(self, n):
        self.typelist(n.nodes[1])
        name = n.nodes[0]
        t_name = self.context.find(name)
        if not t_name:
            self.type_error("Unknown function {}".format(name))
        if t_name.arguments == None:
            self.type_error("Function {} is not callable".format(name))

        actual_argument_types = [ c.type for c in n.nodes[1] ]


        print(name, "args:", t_name)
        valid, concrete_type = check_function_arguments(actual_argument_types, t_name, self.typecontext)
        if valid:
            n.type = concrete_type.type # Return type
        else:
            print(str(t_name))
            print()
            self.type_error("Unknown arguments for {}: Got {}, expected {}".format(
                            name,
                            str(list(map(str, actual_argument_types))),
                            str(t_name)
                ))

    def t_lambda(self, n):
        args = [ c[1] for c in n.nodes[0] ]
        # Body
        self.context.push_frame()
        for arg in n.nodes[0]:
            if self.context.find(arg[0]) != None:
                self.type_error("Argument {} of lambda {} is already defined as variable".format(arg[0], str(n)))
            self.context.set(arg[0], arg[1])
        self.typecheck(n.nodes[1])
        self.context.pop_frame()

        n.type = Type(
            arguments = args,
            type = n.nodes[1].type
        )

    def t_atom(self, n):
        k = self.context.find(n.nodes[0])
        if k == None:
            self.type_error("Unknown variable {}".format(n.nodes[0]))
        n.type = k

    def t_let(self, n):
        self.typecheck(n.nodes[1])
        n.type = n.nodes[1].type
        self.context.set(n.nodes[0], n.type)

    def t_op(self, n):
        if n.nodet in ['&&', '||']:
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
        else:
            self.type_error("Unknown operator {}".format(n.nodet))

    def typecheck(self, n):
        if type(n) == list:
            return self.typelist(n)
        if type(n) == str:
            print(n, "string invalid")
            return n
        if n.nodet == 'type':
            return self.t_type(n)
        elif n.nodet == 'native':
            return self.t_native(n)
        elif n.nodet == 'decl':
            return self.t_decl(n)
        elif n.nodet == 'invocation':
            return self.t_invocation(n)
        elif n.nodet == 'lambda':
            return self.t_lambda(n)
        elif n.nodet == 'atom':
            return self.t_atom(n)
        elif n.nodet == 'let':
            return self.t_let(n)
        elif not n.nodet.isalnum():
            return self.t_op(n)
        elif n.nodet == 'block':
            self.typelist(n.nodes)
            if n.nodes:
                n.type = n.nodes[-1].type
            else:
                n.type = t_v
        elif n.nodet == 'literal':
            pass # Implemented on the frontend
        else:
            print("No TypeCheck rule for", n.nodet)
        return n


def typecheck(ast):
    tc = TypeChecker()
    return tc.typecheck(ast), tc.context.stack[0], tc.typecontext
