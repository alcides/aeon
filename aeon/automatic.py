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
from .frontend import native, decl, expr


POPULATION_SIZE = 10
MAX_GENERATIONS = 3
MAX_DEPTH = 10
ELITISM_SIZE = 5
NOVELTY_SIZE = 5

N_TRIES_REFINEMENT_CHECK = 1000
MAX_TRIES_Z3 = 1000
QUICKCHECK_SIZE = 10
TIMEOUT_RUN = 5

MIN_DOUBLE = -1000000000
MAX_DOUBLE = 1000000000

MIN_INT = -2147483648
MAX_INT = 2147483647

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
        self.random.seed(1)
        self.refined = refined
        
        self.program_evaluator = copy.deepcopy(root)
        self.function_template = get_fun(root, function_name)
        
        self.fitness_evaluator = self.create_evaluator_program(function_name, function_type)
        self.compiled_evaluator = False
        
        self.cached_z3_random = {}
        
        print(20*"-")
        print("GA")
        print(20*"-")
        print("looking for source code that satisfies type", goal_type)
        print("within the context of function", function_name)
        print("with type", function_type)
        print(20*"-")
    

    def compile_condition(self, i, cond, ft):
        
        def replace_invocations(node):
            if type(node) == list:
                for n in node:
                    replace_invocations(n)
            elif type(node) != Node:
                pass
            elif node.nodet == 'invocation':
                fname = node.nodes[0]
                for decl in self.root:
                    if decl.nodet == 'decl' and decl.nodes[0] == fname:
                        node.nodes = list(node.nodes)
                        node.nodes[0] = "Candidate.{}".format(node.nodes[0])
            else:
                for n in node.nodes:
                    replace_invocations(n)
        
        cond = copy.deepcopy(cond)
        replace_invocations(cond)
        
        if cond.nodet == '==':
            fitness_calc = Node('invocation', 'Math.abs', [
                    Node('*', Node('literal', 1.0, type=t_f), Node('-', cond.nodes[0], cond.nodes[1]))
            ])
        else:
            fitness_calc = Node('invocation', 'J.iif', [
                    cond,
                    Node('lambda', [], Node('literal', 0.0, type=t_f)),
                    Node('lambda', [], Node('literal', 1.0, type=t_f))
            ])
        
        main_b = Node('invocation', 'GA.addFitness', [
                Node('literal', i, type=t_i),
                fitness_calc
            ])
        
        
        argnodes = [
            Node('argument', "__argument_{}".format(i), t) for i,t in enumerate(ft.lambda_parameters)
        ]
        argnodes.append(Node('argument', "__return_0", ft.type))
        
        fn_cond = Node('decl',
                    'test{}'.format(i), 
                    argnodes,
                    Node('argument', '_', t_v),
                    None,
                    None,
                    None, 
                    Node('block', main_b))
        return fn_cond

    def prepare_arguments(self, types, tests, counter=0):
        t = types.pop()
        
        if t.conditions and len(t.conditions) > 1:
            lambda_cond_body = reduce(lambda x,y: Node('&&', x, y), t.conditions)
        elif t.conditions:
            lambda_cond_body = t.conditions[0]
        else:
            lambda_cond_body = Node('literal', True, type=t_b)
            
        if types:
            lambda_do_body = self.prepare_arguments(types, tests, counter+1)
        else:
            lambda_do_body = Node('block', *tests)
        
        return Node('invocation', 'GA.genInteger', [
            Node('literal', QUICKCHECK_SIZE, type=t_i), #size
            Node('literal', self.random.randint(0,1000), type=t_i), #seed
            Node('lambda', [ ('__return_0', t.type) ], lambda_cond_body),
            Node('lambda', [ ('__argument_{}'.format(counter), t) ], lambda_do_body)
        ])
        

    def create_evaluator_program(self, fname, ftype):
        tests = [ self.compile_condition(i, cond, ftype) for i, cond in enumerate(ftype.conditions) ]
        
        args = [ Node('atom', '__argument_{}'.format(i)) for i, v in enumerate(ftype.lambda_parameters) ]
        
        call = Node('let', '__return_0', Node('invocation', "Candidate.{}".format(fname), args), ftype.type)
        tests_to_do =  [ Node('invocation', 'test{}'.format(i), [a for a in args]  + [Node('atom', '__return_0')]) for i, cond in enumerate(ftype.conditions) ]
        
        
        fn_targets = []
        for decl in [ c for c in self.root if c.nodet == 'decl']:
            fn_target = copy.deepcopy(decl)
            fn_target.nodet = 'native'
            fn_target.nodes = list(fn_target.nodes)[:-1]
            fn_target.nodes[0] = 'Candidate.{}'.format(decl.nodes[0])
            fn_targets.append(fn_target)
        
        variableIterator = self.prepare_arguments(copy.deepcopy(ftype.lambda_parameters), [call] + tests_to_do)
        
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
        fn_abs = n("native Math.abs : T => (_:Double) -> _:Double")
        helpers = [fn_if, fn_abs]
        p = helpers + fn_targets + [fn_genInteger, fn_getFitness, fn_addFitness, fn_out] + tests + [fn_main]
        self.compile(p, 'FitnessEvaluator', compile_java=False)
        return p
        
    def random_ast(self, tp, depth=0):
        
        def random_int_literal(tp):
            #v = random.randint(-2147483648, 2147483647)
            if depth == 0 and tp.conditions and self.refined:
                key = str(tp)
                if key in self.cached_z3_random:
                    options = self.cached_z3_random[key]
                else:
                    gz = Zed()
                    options = gz.generate_random_type(tp, MAX_TRIES_Z3)
                    self.cached_z3_random[key] = options
                v = random.choice(options).as_long()
            else:
                v = None
            if not v:
                v = int(random.triangular(MIN_INT, MAX_INT))
            return Node('literal', v, type=t_i)
            
        def random_boolean_literal(tp):
            v = random.choice([True, False])
            return Node('literal', v, type=t_b)
            
        def random_double_literal(tp):
            v = random.uniform(MIN_DOUBLE, MAX_DOUBLE)
            return Node('literal', v, type=t_f)
            
        def random_string_literal(tp):
            return Node('literal', "", type=t_s )
            
        def random_let(tp):
            var_name = "var_{}".format(random.randint(0,1000000))
            
            random_type = self.random.choice(self.typechecker.typecontext.types)
            
            df = self.random_ast(random_type, depth+1)
            l = Node('let', var_name, df)
            self.context.push_frame()
            try:
                self.typechecker.typecheck(l)
            except:
                return None
            u = self.random_ast(tp, depth+1)
            self.context.pop_frame()
            return Node('block', l, u)
        
        def random_atom(tp):
            candidates = []
            for v in self.context.variables():
                t = self.context.find(v)
                if not t.lambda_parameters and t == tp:
                    candidates.append(v)
            if not candidates:
                return None
            k = random.choice(candidates)
            return Node('atom', k)
            
        def random_invocation(tp):
            options = []
            for decl in self.context.stack[0]:
                decl_t = self.context.stack[0][decl]
                if decl_t.type == tp: # TODO generic
                    options.append((decl, decl_t))
            if options:
                f, ft = random.choice(options)
                args = [
                    self.random_ast(at, depth+1)
                    for at in ft.lambda_parameters ]
                if all(args):
                    return Node('invocation', f, args)
            else:
                return None
            
            
        def random_operator(tp):
            if any([tp == t for t in [t_i, t_f]]):
                op = self.random.choice(['+', '-', '*', '/', '%'])
                t_a = tp == t_i and t_i or self.random.choice([t_i, t_f])
                a1 = self.random_ast(t_a, depth+1)
                if op == '/':
                    if t_a == t_i:
                        t_a.add_condition(expr.parse_strict('__return_0 != 0'))
                    if t_a == t_f:
                        t_a.add_condition(expr.parse_strict('__return_0 != 0.0'))
                a2 = self.random_ast(t_a, depth+1)
                return Node(op, a1, a2)
            elif tp == t_b:
                a1 = self.random_ast(t_b, depth+1)
                a2 = self.random_ast(t_b, depth+1)
                return Node(self.random.choice(['&&', '||']), a1, a2)
            else:
                return None
        
        possible_generators = []
        if tp == t_i:
            possible_generators.append(random_int_literal)
        if tp == t_b:
            possible_generators.append(random_boolean_literal)
        if tp == t_f:
            possible_generators.append(random_double_literal)
        if tp == t_s:
            possible_generators.append(random_string_literal)
        
        if depth >= MAX_DEPTH:
            if possible_generators:
                return random.choice(possible_generators)(tp)
            else:
                print("Could not finish ", tp)

        if any([tp == t for t in [t_i, t_f, t_b]]):
            possible_generators.append(random_operator)
        
        if self.context.variables():
            possible_generators.append(random_atom)
            
        possible_generators.append(random_invocation)
        possible_generators.append(random_let)
        
        if not possible_generators:
            raise Exception("Could not generate random code for type {}", tp)
        k = None
        while not k:
            k = random.choice(possible_generators)(tp) 
        return k
        
    
    def random_individual(self):
        for i in range(N_TRIES_REFINEMENT_CHECK):
            c = self.random_ast(tp=self.type)
            if c and self.validate(c):
                return c
        raise Exception("Could not generate AST for type {}".format(self.type))
    
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
        ast, context, tcontext = typecheck(program, refined=False) #, refined=False
        output = generate(ast, context, tcontext, class_name=name, generate_file=True)
        
        if compile_java:
            compilation = "javac -Xdiags:verbose -cp AeminiumRuntime.jar:. {}.java".format(name)
            subprocess.call(compilation, cwd="bin", shell=True)
    
    def run_and_retrieve_fitness(self, program):
        try:
            self.compile(program, 'Candidate')
            
            
            compilation = "javac -Xdiags:verbose -cp AeminiumRuntime.jar:. Candidate.java"
            ce = subprocess.run(compilation, cwd="bin", shell=True)
            if ce.returncode != 0:
                subprocess.run("cp Candidate.java CandidateError.java", cwd="bin", shell=True)
                print("Failed to compile")
                print(program)
                return MAX_DOUBLE
            
            if not self.compiled_evaluator:
                self.compiled_evaluator = True
                compilation = "javac -Xdiags:verbose -cp AeminiumRuntime.jar:. FitnessEvaluator.java"
                subprocess.call(compilation, cwd="bin", shell=True)
                
            
            
            program = "java -cp AeminiumRuntime.jar:. FitnessEvaluator".split(" ")
            a = subprocess.check_output(program, cwd="bin", timeout=TIMEOUT_RUN).strip()
            print(float(a))
            return float(a)
        except Exception as e:
            raise e
            return MAX_DOUBLE
    
    def evaluate(self, population):
        evalutator_names = []
        candidate_map = {}
        

        
        for i, candidate in enumerate(population):
            program_evaluator = copy.deepcopy(self.program_evaluator)
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
            self.evaluate(population)
            
            old_population = sorted(population, key=lambda x: x.fitness)
            
            
            
            population = old_population[:ELITISM_SIZE] + [ self.random_individual() for i in range(NOVELTY_SIZE) ]
            

        self.evaluate(population)        
        return [ self.clean(p) for p in population]
        

def synthesise(hole, goal_type, root, context, function_name, function_type, typechecker, rand=None, refined=False):
    s = Synthesiser(hole, goal_type, root, context, function_name, function_type, typechecker, rand, refined)
    
    candidates = s.evolve()

    print("Found {} suitable definitions".format(len(candidates)))
    for approved in candidates:
        print(pp(approved), "[Fitness:", approved.fitness, "]")
    
    if not candidates:
        raise Exception("Hole unknown")
    
    return candidates[0]