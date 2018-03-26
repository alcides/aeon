import copy
import random
from .typechecker import typecheck
from .typestructure import *
from .prettyprinter import prettyprint as pp

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
    
def validate_candidate(candidate, f, template):
    nf = replace_hole(f, candidate)
    program_wrapper = copy.deepcopy(program_evaluator)
    program_wrapper.append(nf)
    try:
        typecheck(program_wrapper)
        return nf
    except:
        return None
    

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
    

    def random_ast(self, type):
        r = self.random.random()
        if r < 0.5 and any([ type == t for t in [t_i, t_b, t_f] ]): # Literal
            if type == t_i:
                v = random.randint(-2147483648, 2147483647)
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
    
    def evolve(self):
        self.random_ast(self.type)
        return None
        

def synthesise(hole, goal_type, root, context, function_name, function_type, typechecker, rand=None):
    s = Synthesiser(hole, goal_type, root, context, function_name, function_type, typechecker, rand)
    print(s.evolve())
    
    
    print("looking for source code that satisfies type", goal_type)
    print("within the context of function", function_name)
    print("with type", function_type)
    
    
    candidates = [ Node('literal', nodes=[str(i)], type=Type('Integer')) for i in range(10) ]
    
    function_template = get_fun(root, function_name)
    program_evaluator = remove_fun(root, function_name)
    
    evalutator_names = []
    candidate_map = {}
    for i, candidate in enumerate(candidates):
        f = copy.deepcopy(function_template)
        f.nodes = list(f.nodes)
        f.name = f.nodes[0] = f.nodes[0] + "_candidate_" + str(i)
        
        nf = replace_hole(f, candidate)
        
        program_wrapper = copy.deepcopy(program_evaluator)
        program_wrapper.append(nf)
        try:
            typecheck(program_wrapper)
            candidate_map[f.name] = candidate
            program_evaluator.append(nf)
        except Exception as e:
            pass # Should be generating a new one.
    for df in program_evaluator:
        print("-->", df)

    print("Found {} suitable definitions".format(len(candidate_map)))
    for approved in candidate_map.values():
        print(pp(approved))
    
    if not candidate_map:
        raise Exception("Hole unknown")
    
    return candidate_map[list(candidate_map.keys())[0]]