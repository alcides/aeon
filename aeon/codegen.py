import sys
from .typestructure import *

class Expr(object):
    def __init__(self, text="", is_stmt=False, extra=None):
        self.text = str(text)
        self.is_stmt = is_stmt
        self.extra=extra

    def __str__(self):
        return self.text

class Block(object):
    def __init__(self, t):
        self.type = t
        self.stmts = []

    def add(self, stmt):
        self.stmts.append(stmt)

    def __str__(self):
        return self.get_stmts()

    def wrap_noop(self, e):
        if type(e) == Expr:
            if not e.is_stmt:
                return "J.noop(" + str(e) + ")"
            else:
                return str(e)
        else:
            return e

    def get_stmts(self):
        return "\n".join(map(lambda x: self.wrap_noop(x)+";", self.stmts))


class CodeGenerator(object):
    def __init__(self, context, typecontext, class_name = 'E'):
        self.table = context.stack[0]
        self.context = context
        self.typecontext = typecontext
        self.stack = [self.table, {}]
        self.blockstack = []
        self.counter = 0
        self.class_name = class_name

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
        
    def wrap_underscore(self, n):
        if n == "_":
            n = "underscore{}".format(self.get_counter())
        return n


    def type_alias_resolver(self, ty):
        for ta in self.typecontext.type_aliases:
            if ta == ty:
                return self.typecontext.type_aliases[ta]
            mapping = ta.polymorphic_matches(ty, self.typecontext)
            if mapping:
                return self.typecontext.type_aliases[ta].polymorphic_fill(mapping)
        return None

    def type_convert(self, t):
        r = self.type_alias_resolver(t)
        if r:
            return self.type_convert(r)
        if type(t) == str:
            t = Type(t)
        if t.lambda_parameters != None:
            #This is a lambda expression
            if len(t.lambda_parameters) == 0:
                return "java.util.function.Supplier<{}>".format(self.type_convert(t.type))
            elif len(t.lambda_parameters) == 1 and t.lambda_parameters[0] == t.type:
                return "java.util.function.UnaryOperator<{}>".format(self.type_convert(t.type))
            elif len(t.lambda_parameters) == 1 and str(t.type) == 'Boolean':
                return "java.util.function.Predicate<{}>".format(self.type_convert(t.lambda_parameters[0]))
            elif len(t.lambda_parameters) == 1 and str(t.type) == 'Void':
                return "java.util.function.Consumer<{}>".format(self.type_convert(t.lambda_parameters[0]))
            elif len(t.lambda_parameters) == 1:
                return "java.util.function.Function<{}, {}>".format(self.type_convert(t.lambda_parameters[0]), self.type_convert(t.type))
            elif len(t.lambda_parameters) == 2 and str(t.type) == 'Boolean':
                return "java.util.function.BiPredicate<{}>".format(self.type_convert(t.lambda_parameters[0]), self.type_convert(t.lambda_parameters[1]))
            elif len(t.lambda_parameters) == 2 and str(t.type) == 'Void':
                return "java.util.function.BiConsumer<{}>".format(self.type_convert(t.lambda_parameters[0]), self.type_convert(t.lambda_parameters[1]))
            elif len(t.lambda_parameters) == 2:
                return "java.util.function.BiFunction<{}, {}, {}>".format(self.type_convert(t.lambda_parameters[0]), self.type_convert(t.lambda_parameters[1]), self.type_convert(t.type))
            else:
                print("Codegen unavaiable for lambdas with type: ", str(t))

        if t.type == 'Array':
            return str(t.type_arguments[0]) + "[]"
        if t.type == 'Void':
            return 'void'
        return self.java_str(t)

    def java_str(self, t):
        bt = str(t.type)
        if t.type_arguments:
            bt += "<" + ", ".join(map(str, t.type_arguments)) + ">"
        return bt

    def root(self, ast):
        return """
        public class {} {{
            {}
        }}
        """.format(self.class_name, self.g_toplevel(ast))

    def genlist(self, ns, *args, **kwargs):
        return "\n".join([ self.generate(n, *args, **kwargs) for n in ns ])

    def java_cost_of(self, tp):
        "Returns the java expression that predicts the cost of a method"
        
        if tp.effects:
            for eff in tp.effects:
                if eff.nodet == 'invocation' and eff.nodes[0] == 'time':
                    c = self.g_expr(eff.nodes[1][0]);
                    return c
        return "0";

    def generate_dispatcher(self, name, versions):
        ftype = self.table[name]
        lrtype = self.type_convert(ftype.type)
        largtypes = ", ".join([ "{} {}".format(self.type_convert(a), "__argument_" + str(i)) for i, a in enumerate(ftype.lambda_parameters)])
        
        invocation_args = "(" + ", ".join([ "{}".format("__argument_" + str(i)) for i, a in enumerate(ftype.lambda_parameters)]) + ")"
        
        inv = ''
        
        # Get costs
        for v in versions:
            inv += "double cost__{} = ({}); \n".format(v[0], self.java_cost_of(v[1]))
            
        for v in versions[:-1]:
            cond = " && ".join([ "cost__{} < cost__{}".format(v[0], v2[0]) for v2 in versions if v2[0] != v[0] ])
            r = ftype.type == 'Void' and '' or 'return '
            inv += "if ({}) {} {}{};".format(cond, r, v[0], invocation_args)
        
            
            
        # Final return
        if not ftype.type == 'Void':
            inv +='return '
            
        inv += versions[-1][0] + invocation_args
        inv += ";"
        body = inv
        return """ public static {} {}({}) {{ {} }}""".format(
            lrtype,
            name,
            largtypes,
            body
        )

    def multiple_dispatch_helpers(self):
        dispatchers = []
        for name in self.context.funs:
            versions = self.context.funs[name]
            if len(versions) > 1:
                dispatchers.append(self.generate_dispatcher(name, versions))
        return "\n\n".join(dispatchers)

    def g_toplevel(self, n):
        """ [decl] """
        return "\n\n".join(map(self.g_decl, n)) + self.multiple_dispatch_helpers()

    def g_decl(self, n):
        """ decl -> string """

        if n.nodet == 'native':
            return ""

        if n.nodet == 'type':
            return "" # Codegeneration of type alias

        name = n.nodes[0]
        
        ftype = self.table[name]
        lrtype = self.type_convert(ftype.type)
        largtypes = ", ".join([ "{} {}".format(self.type_convert(a[1]), self.wrap_underscore(a[0])) for a in n.nodes[1]])
        self.push_frame()
        
        self.block = Block(lrtype)
        self.blockstack.append(self.block)
        
        
        body = self.g_block(n.nodes[6], type=lrtype)
        noop = True
        if name == 'main' and lrtype == 'void' and ftype.lambda_parameters and str(ftype.lambda_parameters[0]) == 'Array<String>':
            body = self.futurify_body(body, lrtype)
            noop = False


        if lrtype != "void":
            if body.extra:
                self.block.add(body)
                body_final = "return {}".format(body.extra)
            else:
                body_final = "return {}".format(body)
        else:
            if n.nodes[6].type != t_v and noop:
                body_final = "J.noop(" + str(body) + ")"
            else:
                body_final = body
        
        self.block.add( Expr(body_final, is_stmt=True) )
        
        body = self.block.get_stmts()
        self.blockstack.pop()
        self.block = None
        self.pop_frame()

        return """ public static {} {}({}) {{ {} }}""".format(
            lrtype,
            n.md_name,
            largtypes,
            body
        )

    def futurify_body(self, body, lrtype):
        
        self.block.stmts.insert(0, Expr("aeminium.runtime.futures.RuntimeManager.init()", is_stmt=True))
        if lrtype == "void":
            self.block.add(body)
            body = Expr("aeminium.runtime.futures.RuntimeManager.shutdown()", is_stmt=True)
        else:
            self.block.add(Expr("{} ret_aeminium_manager = {}".format(lrtype, body), is_stmt=True));
            self.block.add(Expr("aeminium.runtime.futures.RuntimeManager.shutdown()", is_stmt=True));
            body = Expr("ret_aeminium_manager")
        return body


    def g_block(self, n, type='void'):
        for prev in n.nodes[:-1]:
            self.block.add(self.g_expr(prev))
        
        return self.g_expr(n.nodes[-1])
    
    def g_expr(self, n):
        if n.nodet == 'invocation':
            return self.g_invocation(n)
        elif n.nodet == 'literal':
            return self.g_literal(n)
        elif n.nodet == 'let':
            return self.g_let(n)
        elif n.nodet in ["&&", "||", "<", "<=", ">", ">=", "==", "!=", "+", "-", "*", "/", "%"]:
            return self.g_op(n)
        elif n.nodet == 'atom':
            return self.g_atom(n)
        elif n.nodet == 'lambda':
            return self.g_lambda(n)
        elif n.nodet == 'block':
            return self.g_block(n, self.type_convert(n.type))
        elif n.nodet == 'hole':            
            return self.g_expr(n.nodes[0])
        else:
            print("new_type:", n)
            return Expr("X")

    def g_invocation(self, n):
        fname = n.nodes[0]
        if hasattr(n, 'version') and n.version > 0:
            fversions = self.context.funs[fname]
            fname = fversions[n.version - 1][0]
        return Expr("""
            {}({})
        """.format(
            fname,
            ", ".join([str(self.g_expr(x)) for x in n.nodes[1]])
        ), is_stmt=n.type == 'Void')

    def g_atom(self, n):
        if "__index__" in n.nodes[0]:
            target_string, prop_name = n.nodes[0].split("__index__")
            target_type = self.find(target_string)
            prop = self.typecontext.get_type_property(target_type, prop_name)
            if prop:
                return Expr(prop[2] + "(" + target_string + ")")
        
        return Expr(self.wrap_underscore(n.nodes[0]))

    def g_let(self, n):
        var_name = n.nodes[0]
        var_type = self.type_convert(n.type)
        var_value = self.g_expr(n.nodes[1])
        
        if self.find(var_name) != None:
            return Expr("{} = {}".format(var_name, str(var_value)), is_stmt=True, extra=var_name)
        else:
            self.stack[-1][var_name] = var_type
            return Expr("{} {} = {}".format(var_type, var_name, str(var_value)), is_stmt=True, extra=var_name)

    def g_lambda(self, n):
        args = ", ".join([ "{} {}".format(self.type_convert(i[1]), i[0]) for i in n.nodes[0] ])
        rtype = n.type.type
        
        self.block = Block(rtype)
        self.blockstack.append(self.block)

        body = self.g_expr(n.nodes[1])
        
        if rtype != t_v:
            if body.extra:
                self.block.add(body)
                body_final = "return {}".format(body.extra)
            else:
                body_final = "return {}".format(body)
        else:
            if n.nodes[1].type != t_v:
                body_final = "J.noop(" + str(body) + ")"
            else:
                body_final = body
        
        self.block.add( Expr(body_final, is_stmt=True) )
        
        body = self.block.get_stmts()
        self.blockstack.pop()
        self.block = self.blockstack[-1]
                
        return Expr("({}) -> {{ {} }}".format(args, body))


    def g_literal(self, n):
        
        return Expr("({})".format(str(n.nodes[0]).lower()))


    def g_op(self, n):
        if len(n.nodes) == 2:
            return Expr("({1} {0} {2})".format(
                n.nodet,
                self.g_expr(n.nodes[0]),
                self.g_expr(n.nodes[1])
            ))
        else:
            return Expr("({0} {1})".format(
                n.nodet,
                self.g_expr(n.nodes[0])
            ))


def generate(ast, table, typecontext, class_name='E', generate_file=False):
    output = CodeGenerator(table, typecontext, class_name).root(ast)
    try:
        os.mkdir('bin')
    except:
        pass
    open('bin/{}.java'.format(class_name), 'w').write(output)
    return output
    
