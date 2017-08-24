from .typestructure import *
from .java import type_convert

class Expr(object):
    def __init__(self, text="", is_stmt=False):
        self.text = text
        self.is_stmt = is_stmt

    def __str__(self):
        return self.text

class Block(object):
    def __init__(self, t):
        self.type = t
        self.stmts = []
        self.escape = None

    def add(self, stmt):
        self.stmts.append(stmt)

    def __str__(self):
        return self.get_stmts()

    def get_escape(self):
        if self.type == 'void':
            return ""
        if not self.escape and self.stmts:
            self.escape = self.stmts.pop()
        return self.escape

    def get_stmts(self):
        return "\n".join(map(lambda x: x+";", self.stmts))


class CodeGenerator(object):
    def __init__(self, table):
        self.table = table
        self.stack = [table, {}]
        self.blockstack = []
        self.counter = 0

    def push_frame(self):
        self.stack.append({})

    def pop_frame(self):
        self.stack = self.stack[:-1]

    def find(self, kw):
        for frame in self.stack[::-1]:
            if kw in frame:
                return frame[kw]
        return None

    def get_counter(self):
        self.counter += 1
        return self.counter

    def root(self, ast):
        return """
        public class E {{
            {}
        }}
        """.format(self.g_toplevel(ast))

    def genlist(self, ns, *args, **kwargs):
        return "\n".join([ self.generate(n, *args, **kwargs) for n in ns ])

    def g_toplevel(self, n):
        """ [decl] """
        return "\n\n".join(map(self.g_decl, n))

    def g_decl(self, n):
        """ decl -> string """
        name = n.nodes[0]
        ftype = self.table[name]
        lrtype = type_convert(ftype.rtype)
        largtypes = ", ".join([ "{} {}".format(type_convert(a[1]), a[0]) for a in n.nodes[1]])

        body = self.g_block(n.nodes[3], type=lrtype)

        body = self.futurify_body(body, lrtype)

        if lrtype != "void":
            body_final = "return {};".format(body.get_escape())
        else:
            body_final = ""

        return """ public static {} {}({}) {{ {} \n {} }}""".format(
            lrtype,
            name,
            largtypes,
            body.get_stmts(),
            body_final
        )

    def futurify_body(self, body, lrtype):
        body.stmts.insert(0, "aeminium.runtime.futures.RuntimeManager.init()");
        if lrtype == 'void':
            body.stmts.append("aeminium.runtime.futures.RuntimeManager.shutdown()");
        else:
            body.stmts.append("{} ret_aeminium_manager = {}".format(lrtype, body.get_escape()));
            body.stmts.append("aeminium.runtime.futures.RuntimeManager.shutdown()");
            body.escape = "ret_aeminium_manager"
        return body


    def g_block(self, n, type='void'):
        b = Block(type)
        self.blockstack.append(b)
        for c in n.nodes:
            e = self.g_expr(c)
            if c != n.nodes[-1] and c.type != t_v and not e.is_stmt:
                b.add("J.noop(" + str(self.g_expr(c)) + ")")
            else:
                b.add(str(self.g_expr(c)))
        self.blockstack.pop()
        return b

    def g_expr(self, n):
        if n.nodet == 'invocation':
            return self.g_invocation(n)
        elif n.nodet == 'literal':
            return self.g_literal(n)
        elif n.nodet == 'let':
            return self.g_let(n)
        elif n.nodet in ["<", "<=", ">", ">=", "==", "!=", "+", "-", "*", "/", "%"]:
            return self.g_op(n)
        elif n.nodet == 'atom':
            return self.g_atom(n)
        elif n.nodet == 'lambda':
            return self.g_lambda(n)
        elif n.nodet == 'block':
            return self.g_block(n, type_convert(n.type))
        else:
            print("new_type:", n)
            return Expr("Wow")

    def g_invocation(self, n):
        return Expr("""
            {}({})
        """.format(
            n.nodes[0],
            ", ".join([str(self.g_expr(x)) for x in n.nodes[1]])
        ), is_stmt=True)

    def g_atom(self, n):
        return Expr(n.nodes[0])

    def g_let(self, n):
        var_name = n.nodes[0]
        var_type = type_convert(n.type)
        var_value = self.g_expr(n.nodes[1])
        return Expr("{} {} = {}".format(var_type, var_name, str(var_value)), is_stmt=True)

    def g_lambda(self, n):
        # TODO: args
        p2 = self.g_expr(n.nodes[1])
        if type(p2) == Block:
            esc = p2.get_escape()
            if esc:
                body = "{{ {}; return {}; }}".format(p2.get_stmts(), esc)
            else:
                body = "{{ {} }}".format(p2.get_stmts())
        else:
            body = str(p2)
        return Expr("() -> {}".format(body))


    def g_literal(self, n):
        return Expr(str(n.nodes[0]))


    def g_op(self, n):
        return Expr("({1} {0} {2})".format(
            n.nodet,
            self.g_expr(n.nodes[0]),
            self.g_expr(n.nodes[1])
        ))


def generate(ast, table):
    return CodeGenerator(table).root(ast)
