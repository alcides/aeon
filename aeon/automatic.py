import copy
import random
import sys
import subprocess
from functools import reduce
from .typechecker import typecheck
from .typestructure import *
from .prettyprinter import prettyprint as pp
from .codegen import generate
from .zed import Zed, zed
from .frontend import native, decl, expr


POPULATION_SIZE = 50
MAX_GENERATIONS = 50
MAX_DEPTH = 15
ELITISM_SIZE = 2
NOVELTY_SIZE = 5
TOURNAMENT_SIZE = 3

PROB_XOVER = 0.75
PROB_MUT = 0.5

N_TRIES_REFINEMENT_CHECK = 100
MAX_TRIES_Z3 = 100
QUICKCHECK_SIZE = 100
TIMEOUT_RUN = 5

MIN_DOUBLE = -100
MAX_DOUBLE = 100

MIN_INT = -1000
MAX_INT = 1000


def t_i_c():
    return copy.deepcopy(t_i)
    
def t_b_c():
    return copy.deepcopy(t_b)
    
def t_f_c():
    return copy.deepcopy(t_f)

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
        
        self.recursion_allowed = False
        
        print(20*"-")
        print("GA")
        print(20*"-")
        print("looking for source code that satisfies type", goal_type)
        print("within the context of function", function_name)
        print("with type", function_type)
        print(20*"-")
    
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
            return float(a)
        except Exception as e:
            return 2147483648

    def compile_condition(self, i, cond, ft):
        
        if self.depends_on_indices(cond):
            return None
        
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
                    Node('*', Node('literal', 1.0, type=t_f_c()), Node('-', cond.nodes[0], cond.nodes[1]))
            ])
        else:
            fitness_calc = Node('invocation', 'J.iif', [
                    cond,
                    Node('lambda', [], Node('literal', 0.0, type=t_f_c())),
                    Node('lambda', [], Node('literal', 1.0, type=t_f_c()))
            ])
        
        main_b = Node('invocation', 'GA.addFitness', [
                Node('literal', i, type=t_i_c()),
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

    def depends_on_indices(self, c, middle="__index__"):
        if type(c) == list:
            return any([ self.depends_on_indices(n, middle) for n in c ])
        if type(c) != Node:
            return False
        if c.nodet in ['atom']:
            if middle in c.nodes[0]:
                return True
            else:
                return False
        else:
            status = any([ self.depends_on_indices(n, middle) for n in c.nodes ])
        return status

    def prepare_arguments(self, types, tests, counter=0):
        t = types.pop(0)
        
        if t.conditions:
            conditions_to_consider = [ c for c in t.conditions if not self.depends_on_indices(c) ]
        else:
            conditions_to_consider = []
        
        if len(conditions_to_consider) > 1:            
            cs = [ c for c in t.conditions if not self.depends_on_indices(c) ]
            print(cs)
            lambda_cond_body = reduce(lambda x,y: Node('&&', x, y), cs)
        elif len(conditions_to_consider) == 1:            
            lambda_cond_body = t.conditions[0]
        else:
            lambda_cond_body = Node('literal', True, type=t_b_c())
            
        if types:
            lambda_do_body = self.prepare_arguments(types, tests, counter+1)
        else:
            lambda_do_body = Node('block', *tests)
        
        if t == t_i:
            return Node('invocation', 'GA.genInteger', [
                Node('literal', QUICKCHECK_SIZE, type=t_i_c()), #size
                Node('literal', self.random.randint(0,1000), type=t_i_c()), #seed
                Node('lambda', [ ('__return_0', t.type) ], lambda_cond_body),
                Node('lambda', [ ('__argument_{}'.format(counter), t) ], lambda_do_body)
            ])
        else:
            return Node('invocation', 'GA.genObject', [
                Node('literal', QUICKCHECK_SIZE, type=t_i_c()), #size
                self.random_ast(t, constructors_only=True), #object
                Node('lambda', [ ('__return_0', t) ], lambda_cond_body),
                Node('lambda', [ ('__argument_{}'.format(counter), t) ], lambda_do_body)
            ])
        

    def create_evaluator_program(self, fname, ftype):
        
        dependencies = [ nat
            for nat in self.root if nat.nodet in ['native', 'type']
        ]
        
        tests = [ self.compile_condition(i, cond, ftype) for i, cond in enumerate(ftype.conditions) ]
        
        args = [ Node('atom', '__argument_{}'.format(i)) for i, v in enumerate(ftype.lambda_parameters) ]
        
        call = Node('let', '__return_0', Node('invocation', "Candidate.{}".format(fname), args), ftype.type)
        tests_to_do =  [ Node('invocation', 'test{}'.format(i), [a for a in args]  + [Node('atom', '__return_0')]) for i, cond in enumerate(ftype.conditions) if tests[i] ]
        tests = [ t for t in tests if t ]
        
        
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
        fn_genObject = n("native GA.genObject : T => (_:Integer, _:T, _:(T) -> Boolean, _:(T) -> Void) -> _:Void")
        fn_out = n("native System.out.println : (_:Double) -> _:Void")
        fn_addFitness = n("native GA.addFitness : (_:Integer, _:Double) -> _:Double")
        fn_getFitness = n("native GA.getFitness : () -> _:Double")
        fn_if = n("native J.iif : T => (_:Boolean, _: () -> T, _:() -> T) -> _:T")
        fn_abs = n("native Math.abs : T => (_:Double) -> _:Double")
        helpers = [fn_if, fn_abs]
        p = dependencies +  helpers + fn_targets + [fn_genInteger, fn_genObject, fn_getFitness, fn_addFitness, fn_out] + tests + [fn_main]
        
        p = self.filter_duplicate_natives(p)
        
        self.compile(p, 'FitnessEvaluator', compile_java=False)
        return p
    
    def filter_duplicate_natives(self, candidates):
        passed = []
        for d in candidates:
            if d.nodet != 'native':
                passed.append(d)
            else:
                add = True
                for p in passed:
                    if p.nodet == 'native' and p.nodes[0] == d.nodes[0]:
                        add = False
                if add:
                    passed.append(d)
        return passed
        
    def random_ast(self, tp, depth=0, max_depth=MAX_DEPTH, constructors_only=False):
        
        def random_int_literal(tp, **kwargs):
            def wrap(v):
                if v > MAX_INT:
                    return MAX_INT
                if v < MIN_INT:
                    return MIN_INT
                return v
            v = wrap(int(random.gauss(0,(MAX_INT - MIN_INT)/3.0)))
            if tp.conditions and self.refined:
                key = str(tp)
                if key in self.cached_z3_random:
                    options = self.cached_z3_random[key]
                else:
                    gz = copy.deepcopy(zed)
                    options = gz.generate_random_type(tp, MAX_TRIES_Z3)
                    self.cached_z3_random[key] = options
                if options:
                    v = random.choice(options).as_long()
            return Node('literal', v, type=t_i_c())
            
        def random_boolean_literal(tp, **kwargs):
            v = random.choice([True, False])
            return Node('literal', v, type=t_b_c())
            
        def random_double_literal(tp, **kwargs):
            v = random.gauss(0,(MAX_DOUBLE - MIN_DOUBLE)/3.0)
            return Node('literal', v, type=t_f_c())
            
        def random_string_literal(tp, **kwargs):
            return Node('literal', "\"\"", type=t_s ) #TODO
            
        def random_let(tp, **kwargs):
            var_name = "var_{}".format(random.randint(0,1000000))
            
            random_type = self.random.choice(self.typechecker.typecontext.types)
            
            df = self.random_ast(random_type, depth+1)
            l = Node('let', var_name, df)
            self.context.push_frame()
            self.context.set(var_name, random_type)
            u = self.random_ast(tp, depth+1)
            self.context.pop_frame()
            return Node('block', l, u)
        
        def random_atom(tp, **kwargs):
            candidates = []
            for v in self.context.variables():
                t = self.context.find(v)
                if not t.lambda_parameters and t == tp:
                    candidates.append(v)
            if not candidates:
                return None
            k = random.choice(candidates)
            return Node('atom', k)
            
        def random_invocation(tp, no_args=False, **kwargs):
            options = []
            for decl in self.context.stack[0]:
                decl_t = self.context.stack[0][decl]
                if self.typechecker.is_subtype(decl_t.type, tp): # TODO generic
                    if not no_args or decl_t.lambda_parameters == []:
                        if decl != self.function_name or self.recursion_allowed:
                            options.append((decl, decl_t))
            if options:
                f, ft = random.choice(options)
                args = [ self.random_ast(at, depth+1) for at in ft.lambda_parameters ]
                if all(args):
                    return Node('invocation', f, args)
            else:
                return None
            
            
        def random_operator(tp, **kwargs):
            if any([tp == t for t in [t_i, t_f]]):
                op = self.random.choice(['+', '-', '*', '/', '%'])
                t_a = tp == t_i and t_i_c() or self.random.choice([t_i_c(), t_f_c()])
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
        
        if constructors_only:
            possible_generators.append(random_invocation)
            k = None
            while not k:
                k = random.choice(possible_generators)(tp, no_args=True)
            return k

        if tp == t_i:
            possible_generators.append(random_int_literal)
        if tp == t_b:
            possible_generators.append(random_boolean_literal)
        if tp == t_f:
            possible_generators.append(random_double_literal)
        if tp == t_s:
            possible_generators.append(random_string_literal)
        if self.context.variables():
            possible_generators.append(random_atom)
        
        possible_generators.append(random_invocation)
        
        if depth >= max_depth:
            if possible_generators:
                k = random.choice(possible_generators)(tp, no_args=False)
            else:
                print("Could not finish ", tp)


        #if any([tp == t for t in [t_i, t_f, t_b]]):
        #    possible_generators.append(random_operator)
        
        #possible_generators.append(random_let)
        
        if not possible_generators:
            raise Exception("Could not generate random code for type {}", tp)
        k = None
        while not k:
            k = random.choice(possible_generators)(tp)
        return k
        
    
    def random_individual(self, max_depth=MAX_DEPTH):
        for i in range(N_TRIES_REFINEMENT_CHECK):
            c = self.random_ast(tp=self.type, max_depth=max_depth)
            if c and self.validate(c):
                return c
        raise Exception("Could not generate AST for type {}".format(self.type))
    
    def validate(self, candidate):
        f = copy.deepcopy(self.function_template)
        nf = replace_hole(f, candidate)
        
        program_evaluator = copy.deepcopy(self.program_evaluator)
        program = replace_hole(program_evaluator, candidate)
        try:
            typecheck(program, refined=self.refined)
            return nf
        except Exception as e:
            return False
        
    
    def crossover(self, p1, p2, expected=None):
        if not expected:
            expected = self.type
        return self.mutate(copy.deepcopy(p1), source=p2, expected=expected)
        
    def find_nodes(self, tp, node):
        ls = []
        if type(node) == Node:
            if node.type == tp:
                ls.append(node)
            for ch in node.nodes:
                ls.extend(self.find_nodes(tp, ch))
        return ls
            
        
    
    def mutate(self, c, source=None, expected=None):
        if not expected:
            expected = self.type
        
        can_be_source = lambda n: type(n) == list or (type(n) == Node and hasattr(n, 'type')  and n.nodet not in ['atom', 'literal'])
        can_be_replaced = lambda n: type(n) == Node and hasattr(n, 'type')
        repeat = lambda x,i: [x for a in range(i)]
        
        def count_children(n):
            if type(n) == list:
                return sum([ count_children(x) for x in n ])
            elif can_be_replaced(n):
                return 1 + sum([ count_children(x) for x in n.nodes ])
            else:
                return 0
                
        if type(c) == list:
            list_source = c
            def save(i, v):
                c[i] = v
        elif can_be_source(c):
            list_source = c.nodes
            def save(i, v):
                c.nodes = list(c.nodes)
                c.nodes[i] = v
        else:
            return self.random_ast(expected)
                
        indices_to_replace = [ ('h', i) for i in range(len(list_source)) if can_be_replaced(list_source[i]) ]
        for entry in [ repeat(('d', i), count_children(list_source[i])) for i in range(len(list_source))  if can_be_source(list_source[i]) ]:
            indices_to_replace.extend(entry)
        
        if not indices_to_replace:
            return self.random_ast(expected)
        
        w, index = random.choice(indices_to_replace)
        
        if w == 'd':
            if type(c) == list:
                exp = expected[index]
            elif type(c) == Node and c.nodet == 'invocation':
                ft = self.context.find(c.nodes[0])
                exp = ft.lambda_parameters # first argument is parameter list
            else:
                print("TODO")
                exp = list_source[index].type
            save(index, self.mutate(list_source[index], source=source, expected=exp))
        else:
            if type(c) == list:
                expected = expected[index]
            
            target = list_source[index]
            if source:
                options = self.find_nodes(expected, source)
                if options:
                   save(index, self.clean(self.random.choice(options)))
            else:
                save(index, self.random_ast(expected))
        return c
    
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
            
        if hasattr(p.type, 'refined_value'):
            delattr(p.type, 'refined_value')
        
        for n in p.nodes:
            if type(n) == Node:
                self.clean(n)
            
        return p
            
    def tournament(self, population):
        fighters = self.random.sample(population, TOURNAMENT_SIZE)
        return min(fighters, key=lambda x: x.fitness)
        
        
            
    def evolve(self):
        population = [ self.random_individual(max_depth=2) for i in range(POPULATION_SIZE) ]
        
        for i in range(MAX_GENERATIONS):
            print("Generation", i)
            
            self.fitness_evaluator = self.create_evaluator_program(self.function_name, self.function_type)
            self.compiled_evaluator = False
            
            self.evaluate(population)
            
            old_population = sorted(population, key=lambda x: x.fitness)
            
            if old_population[0].fitness == 0.0:
                print("FOUND SOLUTION AT GENERATION", i)
                return [ self.clean(p) for p in old_population[:1]]
            
            for p in old_population[::-1]:
                print("f:", p.fitness, prettyprint(p))
            
            offspring = copy.deepcopy(old_population[:ELITISM_SIZE]) + [ self.random_individual(max_depth=i) for i in range(NOVELTY_SIZE) ]
            
            while len(offspring) < POPULATION_SIZE - ELITISM_SIZE - NOVELTY_SIZE:
                parent1 = self.tournament(old_population)
                if self.random.random() < PROB_XOVER:
                    parent2 = self.tournament(old_population)
                    child = self.crossover(parent1, parent2)
                else:
                    child = parent1
                
                if self.random.random() < PROB_MUT:
                    child = self.mutate(child)
                if self.validate(child):
                    offspring.append(child)
            
            population = offspring
            

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