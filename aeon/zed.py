import sys
from functools import reduce

import z3

from .typestructure import *
from .zed_translate import translate


class AstRefKey:
    def __init__(self, n):
        self.n = n
    def __hash__(self):
        return self.n.hash()
    def __eq__(self, other):
        return self.n.eq(other.n)
    def __repr__(self):
        return str(self.n)

def askey(n):
    assert isinstance(n, z3.AstRef)
    return AstRefKey(n)

def get_z3_vars(st):
    r = set()
    def collect(f):
      if z3.is_const(f): 
          if f.decl().kind() == z3.Z3_OP_UNINTERPRETED and not askey(f) in r:
              r.add(askey(f))
      else:
          for c in f.children():
              collect(c)
    collect(st)
    return list(r)

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
                #´self.solver)
                #print("Failed on ", zc(vars))
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
            return lambda args: True

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
        
    def refine(self, t, new_name, new_context=False, extra=None):
        if hasattr(t, 'refined') and not new_context:
            return (self.context[t.refined], None)
        else:
            if not extra:
                extra = []
            new_expr = reduce(z3.And, [ c([new_name] + extra) for c in t.zed_conditions])
            return (new_name, new_expr)

    def try_subtype(self, t1, t2, new_context=False, under=None):
        if self.is_refined(t1) and self.is_refined(t2):
            self.solver.push()
            self.convert_once(t1)
            self.convert_once(t2)
            
            
            make_new_name = lambda: z3.Int("value_{}".format(self.get_counter()))
            new_name = make_new_name()
            
            (t1_name, t1_assertions) = self.refine(t1, new_name)
            (t2_name, t2_assertions) = self.refine(t2, new_name, new_context=True)
            
            if under:
                (function_type, argtypes) = under
                self.convert_once(function_type)
                
                z_argtypes = [ self.refine(self.convert_once(v), make_new_name()) for v in argtypes ]
                z_argtypes_names = [ t[0] for t in z_argtypes ]
                z_argtypes_expr = [ t[1] for t in z_argtypes ]

                # Post-condition: f_under
                f_name, f_under = self.refine(function_type, new_name, extra=z_argtypes_names)
                postconditions = z3.And(f_under,  t2_assertions)
                
                # Pre-condition: z_argtypes + f_preconditions
                if function_type.zed_pre_conditions:
                    f_preconditions = reduce(z3.And, [ c([f_name] + z_argtypes_names) for c in function_type.zed_pre_conditions], True)
                else:
                    f_preconditions = True
                    

                preconditions = z3.And(reduce(z3.And, [ z for z in z_argtypes_expr if z != None], True), f_preconditions)
                definition = z3.And(t1_name == new_name, reduce(z3.And, copy.deepcopy(self.solver.assertions()), True))
                
                vars = get_z3_vars(preconditions) + get_z3_vars(definition) + get_z3_vars(postconditions)
                vars = [v.n for v in vars]
                
                print("preconditions: ", preconditions)
                print("definition: ", definition)
                print("postconditions: ", postconditions)
                

                s = z3.Solver()
                s.push()
                s.add(z3.ForAll(vars, z3.Implies( 
                        z3.And(preconditions, definition),
                        postconditions
                )))
                
                ver = s.check()
                print("Solver")
                print(s)
                s.pop()
                if ver == z3.unsat:
                    return False
                elif ver == z3.sat:
                    return True
                else:
                    print("Unknown verification", self.solver)
                    return True
                
                def wrap(i, t):
                    a,b = self.refine(self.convert_once(t), new_name)
                    return a
                
                argtypes = [wrap(i, x) for i, x in enumerate(under[1])]
                extra_name, extra_under = self.refine(under[0], new_name, extra=argtypes)
                t2_assertions = z3.And(t2_assertions, extra_under)
                
                if under[0].zed_pre_conditions:
                    extra_pre = reduce(z3.And, [ c([extra_name] + argtypes) for c in under[0].zed_pre_conditions])
                    if t1_assertions == None:
                        t1_assertions = extra_pre
                    else:
                        t1_assertions = z3.And(t1_assertions, extra_pre)
                else:
                    if t1_assertions == None:
                        t1_assertions = True       
        
                definition = t1_assertions
                conclusion = t2_assertions
                variables = argtypes
                
                final = z3.ForAll(variables, z3.Implies(definition, conclusion))
                self.solver.push()
                self.solver.add(final)

                self.solver.pop()

            
            if t1_assertions != None:
                self.solver.add(t1_assertions)    
            
            hypothesis = t1_name == t2_name
            self.solver.add(hypothesis)
                
            
            self.solver.add( z3.Not(t2_assertions))
            
            r = self.solver.check()
            #if r == z3.unsat:
            #    print(self.solver)
            self.solver.pop()
            if r == z3.sat:
                t1.refined_value = self.solver.model()[t1_name] # Error handling
                return False
        return True
    
    def generate_random_type(self, t, max_tries):
        if self.is_refined(t):
            values = []
            self.solver.push()
            self.convert_once(t)
            
            new_name = z3.Int("v_{}".format(self.get_counter()))
            (t_name, t_assertions) = self.refine(t, new_name)
            if t_assertions != None:
                self.solver.add(t_assertions)   
            r = self.solver.check() 
            i = 0
            while r == z3.sat and i < max_tries:
                v = self.solver.model()[t_name] # Error handling
                values.append(v)
                i += 1
                self.solver.add(t_name != v)
                r = self.solver.check() 
            self.solver.pop()
            return values
        else:
            return None

zed = Zed()
