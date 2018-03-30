import copy
import random
from .typechecker import typecheck
from .typestructure import *
from .prettyprinter import prettyprint as pp
from .zed import Zed


POPULATION_SIZE = 10
MAX_GENERATIONS = 10


N_TRIES_REFINEMENT_CHECK = 1000

def remove_fun(ast, function_name):
    return copy.deepcopy([n for n in ast if not (n.nodet == 'decl' and n.nodes[0] == function_name)])

def get_fun(ast, function_name):
    for n in ast:
        if n.nodet == 'decl' and n.nodes[0] == function_name:
            return n
    return None
    
def replace_hole(context, replacement):
    if type(context) == list:
        return [replace_hole(x, replacement) for x in context]
    elif type(context) != Node:
        return context
    elif context.nodet == 'hole':
        return replacement
    context.nodes = [replace_hole(x, replacement) for x in context.nodes]
    return context
    

class Synthesiser(object):
    def __init__(self, hole, goal_type, root, context, function_name, function_type, typechecker, rand):
        self.hole = hole
        self.type = copy.deepcopy(goal_type)
        self.root = root
        self.context = context
        self.function_name = function_name
        self.function_type = function_type
        self.typechecker = typechecker
        self.random = rand or random
        
        self.program_evaluator = remove_fun(root, function_name)
        self.function_template = get_fun(root, function_name)
        
        print(20*"-")
        print("GA")
        print(20*"-")
        print("looking for source code that satisfies type", goal_type)
        print("within the context of function", function_name)
        print("with type", function_type)
        print(20*"-")
    

    def random_ast(self, type):
        r = self.random.random()
        if r < 1.5 and any([ type == t for t in [t_i, t_b, t_f] ]): # Literal
            if type == t_i:
                #v = random.randint(-2147483648, 2147483647)
                
                if type.conditions:
                    gz = Zed()
                    v = gz.generate_random_type(type).as_long()
                else:
                    v = None
                
                if not v:
                    v = int(random.triangular(-2147483648, 2147483647))
                
                return Node('literal', nodes=[str(v)], type=t_i)
            elif type == t_b:
                v = random.choice(['true', 'false'])
                return Node('literal', nodes=[v], type=t_b)
            else:
                v = random.uniform(-10000000, 10000000)
                return Node('literal', nodes=[str(v)], type=t_f)                
        else: # Function:Call
            pass #TODO
        
        possible = any([ t == type for t in self.typechecker.typecontext.types ])
        if not possible:
            raise Exception("Could not generate code for type {}", type)
    
    def random_individual(self):
        for i in range(N_TRIES_REFINEMENT_CHECK):
            c = self.random_ast(type=self.type)
            if c and self.validate(c):
                return c
        print("T", self.type, c, ".", self.validate(c), i)
        raise Exception("Could not generate AST for type {}", str(self.type))
    
    def validate(self, candidate):
        # def validate_candidate(candidate, f, template):
        f = copy.deepcopy(self.function_template)
        nf = replace_hole(f, candidate)
        program_wrapper = copy.deepcopy(self.program_evaluator)
        program_wrapper.append(nf)
        try:
            print("_--")
            print(program_wrapper)
            print("...")
            typecheck(program_wrapper)
            return nf
        except:
            return False
        
    
    def mutate(self, i):
        return self.random_individual()
        
    
    def evaluate(self, population):
        evalutator_names = []
        candidate_map = {}
        for i, candidate in enumerate(population):
            f = copy.deepcopy(self.function_template)
            f.nodes = list(f.nodes)
            f.name = f.nodes[0] = f.nodes[0] + "_candidate_" + str(i)
            nf = replace_hole(f, candidate)
        
            program_wrapper = copy.deepcopy(self.program_evaluator)
            program_wrapper.append(nf)
            try:
                typecheck(program_wrapper)
                candidate_map[f.name] = candidate
                program_evaluator.append(nf)
            except Exception as e:
                pass # Should be generating a new one.
                
        for df in self.program_evaluator:
            print("-->", df)
            
    def clean(self, p):
        if hasattr(p.type, 'refined'):
            delattr(p.type, 'refined')
        return p
            
    def evolve(self):
        population = [ self.random_individual() for i in range(POPULATION_SIZE) ]
        
        for i in range(MAX_GENERATIONS):
            print("Generation", i)
            population = [ self.mutate(i) for i in population ]
            
            self.evaluate(population)
        
        return [ self.clean(p) for p in population]
        

def synthesise(hole, goal_type, root, context, function_name, function_type, typechecker, rand=None):
    s = Synthesiser(hole, goal_type, root, context, function_name, function_type, typechecker, rand)
    
    candidates = s.evolve()

    print("Found {} suitable definitions".format(len(candidates)))
    for approved in candidates:
        print(pp(approved))
    
    if not candidates:
        raise Exception("Hole unknown")
    
    return candidates[0]