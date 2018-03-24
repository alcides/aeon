import sys
from functools import reduce

import z3

from .typestructure import *
from .zed_translate import translate



class Zed(object):
    def __init__(self):
        self.vars = {}
        self.solver = z3.Solver()
        self.counter = 0
        self.hook = None
        self.context = {}
        
    def copy_assertions(self):
        return self.solver.assertions()

    def clean_context(self):
        self.context = {}

    def set_error_hook(self, hook):
        self.hook = hook

    def get_counter(self):
        self.counter += 1
        return self.counter

    def get(self, n):
        return self.context[n]

    def is_refined(self,t):
        ir = t == Type('Double') or t == Type('Integer') or (hasattr(t,'conditions') and t.conditions) # TODO: Clean this up
        return bool(ir)

    def z3_type_constructor(self, t):
        if t == Type('Double'):
            return z3.Real
        elif t == Type('Integer'):
            return z3.Int
        elif t == Type('Boolean'):
            return z3.Bool
        else:
            return z3.Int
            # TODO
            raise Exception("Unknown Type Constructor", t)

    def assert_if(self, r, a, b):
        rn = self.get(r.refined)
        an = self.get(a.type.refined)
        bn = self.get(b.type.refined)
        self.solver.add( z3.Or(rn == an, rn==an) )
        r = self.solver.check()
        assert(r == z3.sat)

    def refine_function_invocation(self, ft, argts):
        
        self.convert_once(ft)
        invocation_name = None

        return_type = ft.type
            
        vars = []
        
        # TODO: for arrays this needs to be true
        if self.is_refined(return_type):
            invocation_name = "return_of_invocation_{}".format(self.get_counter())
            invocation_var = self.z3_type_constructor(return_type)(invocation_name)
            self.context[invocation_name] = invocation_var

            vars.append(invocation_var)
        else:
            vars.append(None)

        for ar in argts:
            if self.is_refined(ar):
                vars.append(self.context[ar.refined])
            else:
                vars.append(None)

        zcs = []
        if ft.preconditions:
            zcs.extend(ft.zed_pre_conditions)
        if ft.conditions:
            zcs.extend(ft.zed_conditions)

  
        for zc in zcs:
            statement = zc(vars)
            self.solver.push()
            self.solver.add(statement)
            r = self.solver.check()
            self.solver.pop()
            if r == z3.unsat:
                print(self.solver)
                print("Failed on ", zc(vars))
                return False, None
            elif r == z3.sat:
                self.solver.add(statement)
        return True, invocation_name


    def refine_atom(self, t):
        self.convert_once(t)
        if self.is_refined(t):
            atom_name = "atom_{}_{}".format(t.type, self.get_counter())
            atom_var = self.z3_type_constructor(t)(atom_name)
            self.context[atom_name] = atom_var
            v = reduce(z3.And, [ c([atom_var]) for c in t.zed_conditions ])
            self.solver.add(v)
            return atom_name

    def make_literal(self, t, v):
        lit_name = "literal_{}_{}".format(t.type, self.get_counter())
        lit_var = self.z3_type_constructor(t)(lit_name)
        self.context[lit_name] = lit_var # TODO: production
        
        self.solver.add(lit_var == v)
        return lit_name

    def combine(self, t, nodet, nodes):
        combiner_name = "op_{}_{}".format(t.type, self.get_counter())
        combiner_var = self.z3_type_constructor(t)(combiner_name)
        self.context[combiner_name] = combiner_var

        if len(nodes) == 2 and self.is_refined(nodes[0].type) and self.is_refined(nodes[1].type):
            ar = nodes[0].type.refined
            br = nodes[1].type.refined

            if nodet == '+':
                a = self.context[ar]
                b = self.context[br]
                self.solver.add( combiner_var == a + b )
            elif nodet == '-':
                a = self.context[ar]
                b = self.context[br]
                self.solver.add( combiner_var == a - b )
            elif nodet == '*':
                a = self.context[ar]
                b = self.context[br]
                self.solver.add( combiner_var == a * b )
            elif nodet == '/':
                a = self.context[ar]
                b = self.context[br]
                self.solver.add( combiner_var == a / b )
            elif nodet == '%':
                a = self.context[ar]
                b = self.context[br]
                self.solver.add( combiner_var == a % b )
            else:
                print("TODO zed", nodet)
        elif self.is_refined(nodes[0].type):
            ar = nodes[0].type.refined
            if nodet == '+':
                a = self.context[ar]
                self.solver.add( combiner_var == 0 + a )
            elif nodet == '-':
                a = self.context[ar]
                self.solver.add( combiner_var == 0 - a )
        return combiner_name

    def universe(self, t):
        if t.type == 'Integer':
            return lambda args: z3.Or(args[0] == 0, args[0] != 0)
        elif t.type == 'Double':
            return lambda args: z3.Or(args[0] == 0, args[0] != 0)
        else:
            return lambda args: None

    def convert_once(self, t):
        if hasattr(t, 'zed_conditions'):
            return t

        if t.preconditions:
            t.zed_pre_conditions = translate(t.preconditions)
        else:
            t.zed_pre_conditions = []

        if t.conditions:
            t.zed_conditions = translate(t.conditions)
        else:
            t.zed_conditions = []
        if not t.zed_conditions:
            t.zed_conditions = [ self.universe(t) ]
        return t

    def try_subtype(self, t1, t2, new_context=False, under=None):
        if self.is_refined(t1) and self.is_refined(t2):
            self.solver.push()
            self.convert_once(t1)
            self.convert_once(t2)
            
            if under:
                self.convert_once(under[0])
            
            new_name = z3.Int("v_{}".format(self.get_counter()))
            def refine(t, new_context=False, extra=None): 
                if hasattr(t, 'refined') and not new_context:
                    return (self.context[t.refined], None)
                else:
                    if not extra:
                        extra = []
                    new_expr = reduce(z3.And, [ c([new_name] + extra) for c in t.zed_conditions])
                    return (new_name, new_expr)
            
            (t1_name, t1_assertions) = refine(t1)
            (t2_name, t2_assertions) = refine(t2, new_context)
            if under:
                def wrap(i, t):
                    a,b = refine(self.convert_once(t))
                    return a
                
                argtypes = [wrap(i, x) for i, x in enumerate(under[1])]
                extra_name, extra_under = refine(under[0], extra=argtypes)
                t2_assertions = z3.And(t2_assertions, extra_under)
                
                if under[0].zed_pre_conditions:
                    extra_pre = reduce(z3.And, [ c([extra_name] + argtypes) for c in under[0].zed_pre_conditions])
                    if t1_assertions == None:
                        t1_assertions = extra_pre
                    else:
                        t1_assertions = z3.And(t1_assertions, extra_pre)

            
            if t1_assertions != None:
                self.solver.add(t1_assertions)    
            
            hypothesis = t1_name == t2_name
            self.solver.add(hypothesis)
                
            self.solver.add( z3.Not(t2_assertions))
            
            r = self.solver.check()
            self.solver.pop()
            if r == z3.sat:
                t1.refined_value = self.solver.model()[t1_name] # Error handling
                return False
            
        return True

zed = Zed()
