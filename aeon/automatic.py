import copy
import random
import sys
import subprocess
from functools import reduce
from .typechecker import typecheck
from .typestructure import *
from .prettyprinter import prettyprint as pp
from .codegen import generate
from .zed import Zed
from .frontend import native, decl


POPULATION_SIZE = 10
MAX_GENERATIONS = 10


N_TRIES_REFINEMENT_CHECK = 1000

QUICKCHECK_SIZE = 10

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
    def __init__(self, hole, goal_type, root, context, function_name, function_type, typechecker, rand, refined=True):
        self.hole = hole
        self.type = copy.deepcopy(goal_type)
        self.root = root
        self.context = context
        self.function_name = function_name
        self.function_type = function_type
        self.typechecker = typechecker
        self.random = rand or random
        self.refined = refined
        
        self.program_evaluator = copy.deepcopy(root)
        self.function_template = get_fun(root, function_name)
        
        self.fitness_evaluator = self.create_evaluator_program(function_name, function_type)
        self.compiled_evaluator = False
        
        print(20*"-")
        print("GA")
        print(20*"-")
        print("looking for source code that satisfies type", goal_type)
        print("within the context of function", function_name)
        print("with type", function_type)
        print(20*"-")
    

    def compile_condition(self, i, cond, ft):
        main_b = Node('invocation', 'GA.addFitness', [
                Node('literal', i, type='Integer'),
                Node('invocation', 'J.iif', [
                    cond,
                    Node('lambda', [], Node('literal', 0.0, type='Double')),
                    Node('lambda', [], Node('literal', 1.0, type='Double')),
                ])
            ])
        
        print("cond", main_b)
        
        
        argnodes = [
            Node('argument', "__argument_{}".format(i), t) for i,t in enumerate(ft.lambda_parameters)
        ]
        argnodes.append(Node('argument', "__return_0", ft.type))
        
        fn_cond = Node('decl',
                    'test{}'.format(i), 
                    argnodes,
                    Node('argument', '_', Type('Void')),
                    None,
                    None,
                    None, 
                    Node('block', main_b))
        return fn_cond

    def prepare_arguments(self, types, tests, counter=0):
        t = types.pop()
        
        if len(t.conditions) > 1:
            lambda_cond_body = reduce(lambda x,y: Node('&&', x, y), t.conditions)
        elif t.conditions:
            lambda_cond_body = t.conditions[0]
        else:
            lambda_cond_body = Node('literal', True, type='Boolean')
            
        if types:
            lambda_do_body = self.prepare_arguments(types, tests, counter+1)
        else:
            lambda_do_body = Node('block', *tests)
        
        return Node('invocation', 'GA.genInteger', [
            Node('literal', QUICKCHECK_SIZE, type='Integer'), #size
            Node('literal', self.random.randint(0,1000), type='Integer'), #seed
            Node('lambda', [ ('__argument_{}'.format(counter), t.type) ], lambda_cond_body),
            Node('lambda', [ ('__argument_{}'.format(counter), t.type) ], lambda_do_body)
        ])
        

    def create_evaluator_program(self, fname, ftype):
        tests = [ self.compile_condition(i, cond, ftype) for i, cond in enumerate(ftype.conditions) ]
        
        args = [ Node('atom', '__argument_{}'.format(i)) for i, v in enumerate(ftype.lambda_parameters) ]
        
        call = Node('let', '__return_0', Node('invocation', "Candidate.{}".format(fname), args), ftype.type)
        tests_to_do =  [ Node('invocation', 'test{}'.format(i), [a for a in args]  + [Node('atom', '__return_0')]) for i, cond in enumerate(ftype.conditions) ]
        
        toCopy = [ c for c in self.root if c.nodes[0] == fname ][0]
        fn_target = copy.deepcopy(toCopy)
        fn_target.nodet = 'native'
        fn_target.nodes = list(fn_target.nodes)
        fn_target.nodes[0] = 'Candidate.{}'.format(fname)
        
        variableIterator = self.prepare_arguments(ftype.lambda_parameters, [call] + tests_to_do)
        
        main_b = [variableIterator] + [
            Node('invocation', 'System.out.println', [
                Node('invocation', 'GA.getFitness', [])
            ])
        ]
        fn_main = Node('decl',
                    'main', 
                    [Node('argument', 'args', Type('Array', type_arguments=['String']))],
                    Node('argument', '_', Type('Void')),
                    None,
                    None,
                    None, 
                    Node('block', *main_b))
        
        n = native.parse_strict
        fn_genInteger = n("native GA.genInteger : (_:Integer, _:Integer, _:(Integer) -> Boolean, _:(Integer) -> Void) -> _:Void")
        fn_out = n("native System.out.println : (_:Double) -> _:Void")
        fn_addFitness = n("native GA.addFitness : (_:Integer, _:Double) -> _:Double")
        fn_getFitness = n("native GA.getFitness : () -> _:Double")
        fn_if = n("native J.iif : T => (_:Boolean, _: () -> T, _:() -> T) -> _:T")
        p = [fn_if, fn_target, fn_genInteger, fn_getFitness, fn_addFitness, fn_out] + tests + [fn_main]
        self.compile(p, 'FitnessEvaluator', compile_java=False)
        return p
        
    def random_ast(self, tp):
        
        def random_int_literal(tp):
            #v = random.randint(-2147483648, 2147483647)
            if tp.conditions and self.refined:
                gz = Zed()
                v = gz.generate_random_type(tp).as_long()
            else:
                v = None
            if not v:
                v = int(random.triangular(-2147483648, 2147483647))
            return Node('literal', nodes=[str(v)], type=t_i)
            
        def random_boolean_literal(tp):
            v = random.choice(['true', 'false'])
            return Node('literal', nodes=[v], type=t_b)
            
        def random_double_literal(tp):
            v = random.uniform(-10000000, 10000000)
            return Node('literal', nodes=[str(v)], type=t_f)
        
        
        possible_generators = []
        if tp == t_i:
            possible_generators.append(random_int_literal)
        if tp == t_b:
            possible_generators.append(random_boolean_literal)
        if tp == t_f:
            possible_generators.append(random_double_literal)
            

        
        if not possible_generators:
            raise Exception("Could not generate random code for type {}", tp)
        
        return random.choice(possible_generators)(tp)
        
    
    def random_individual(self):
        for i in range(N_TRIES_REFINEMENT_CHECK):
            c = self.random_ast(tp=self.type)
            if c and self.validate(c):
                return c
        raise Exception("Could not generate AST for type {}", str(self.type))
    
    def validate(self, candidate):
        f = copy.deepcopy(self.function_template)
        nf = replace_hole(f, candidate)
        try:
            typecheck(nf, refined=self.refined)
            return nf
        except Exception as e:
            return False
        
    
    def mutate(self, i):
        return self.random_individual()
        
    
    def compile(self, program, name, compile_java=False):
        ast, context, tcontext = typecheck(program, refined=False)
        output = generate(ast, context, tcontext, class_name=name, generate_file=True)
        
        if compile_java:
            compilation = "javac -Xdiags:verbose -cp AeminiumRuntime.jar:. {}.java".format(name)
            subprocess.call(compilation, cwd="bin", shell=True)
    
    def run_and_retrieve_fitness(self, program):
        try:
            self.compile(program, 'Candidate')
            
            
            compilation = "javac -Xdiags:verbose -cp AeminiumRuntime.jar:. Candidate.java"
            subprocess.call(compilation, cwd="bin", shell=True)
            
            if not self.compiled_evaluator:
                self.compiled_evaluator = True
                compilation = "javac -Xdiags:verbose -cp AeminiumRuntime.jar:. FitnessEvaluator.java"
                subprocess.call(compilation, cwd="bin", shell=True)
            
            
            program = "java -cp AeminiumRuntime.jar:. FitnessEvaluator".split(" ")
            a = subprocess.check_output(program, cwd="bin").strip()
            print(float(a))
            return float(a)
        except Exception as e:
            raise e
            return 1000000.0
    
    def evaluate(self, population):
        evalutator_names = []
        candidate_map = {}
        
        program_evaluator = copy.deepcopy(self.program_evaluator)
        
        for i, candidate in enumerate(population):
            program = replace_hole(program_evaluator, candidate)
            candidate.fitness = self.run_and_retrieve_fitness(program)

                
                        
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
        

def synthesise(hole, goal_type, root, context, function_name, function_type, typechecker, rand=None, refined=False):
    s = Synthesiser(hole, goal_type, root, context, function_name, function_type, typechecker, rand, refined)
    
    candidates = s.evolve()

    print("Found {} suitable definitions".format(len(candidates)))
    for approved in candidates:
        print(pp(approved))
    
    if not candidates:
        raise Exception("Hole unknown")
    
    return candidates[0]