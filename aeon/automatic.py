import copy
import string
import random
import sys
import subprocess
import z3
import time
from functools import reduce
from .typechecker import typecheck, TypeException
from .typestructure import *
from .prettyprinter import prettyprint as pp
from .codegen import generate
from .zed import Zed, zed
from .frontend import native, decl, expr, invocation

sys.setrecursionlimit(10000)

POPULATION_SIZE = 100
MAX_GENERATIONS = 100
MAX_DEPTH = 10
ELITISM_SIZE = 1
NOVELTY_SIZE = 0
TOURNAMENT_SIZE = 5

PROB_XOVER = 0.80
PROB_MUT = 0.20

MAX_TRIES_TO_GEN_CHILD = 100  # random generation
N_TRIES_REFINEMENT_CHECK = 100
MAX_TRIES_Z3 = 100
QUICKCHECK_SIZE = 100
TIMEOUT_RUN = 5

MIN_DOUBLE = -1000
MAX_DOUBLE = 1000

MIN_INT = -1000
MAX_INT = 1000


class GenException(Exception):
    pass


class MaxDepthException(GenException):
    pass


class NoPossibleExpressionException(GenException):
    pass


def t_i_c():
    return copy.deepcopy(t_i)


def t_b_c():
    return copy.deepcopy(t_b)


def t_f_c():
    return copy.deepcopy(t_f)


def remove_fun(ast, function_name):
    return copy.deepcopy([
        n for n in ast
        if not (n.nodet == 'decl' and n.nodes[0] == function_name)
    ])


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
    def __init__(self,
                 hole,
                 goal_type,
                 root,
                 context,
                 function_name,
                 function_type,
                 typechecker,
                 rand,
                 refined=True,
                 outputdir="bin"):
        self.hole = hole
        self.type = copy.deepcopy(goal_type)
        self.root = root
        self.context = context
        self.function_name = function_name
        self.function_type = function_type
        self.typechecker = typechecker
        self.typechecker.refined = refined
        self.random = rand or random
        self.random.seed(1)
        self.refined = refined
        self.outputdir = outputdir
        self.var_counter = 0

        if refined:
            self.old_zed = zed.solver.to_smt2()

        self.program_evaluator = copy.deepcopy(root)
        self.function_template = get_fun(root, function_name)

        self.fitness_evaluator = self.create_evaluator_program(
            function_name, function_type)
        self.compiled_evaluator = False
        self.candidate_map = {}

        self.cached_z3_random = {}

        self.recursion_allowed = True

        print(20 * "-")
        print("GP")
        print(20 * "-")
        print("looking for source code that satisfies type", self.type)
        print("within the context of function", function_name)
        print("with type", function_type)
        print(20 * "-")

    def reset_zed(self):
        if self.refined:
            new_solver = z3.Solver()
            new_solver.from_string(self.old_zed)
            zed.solver = new_solver

    def next_var(self):
        self.var_counter += 1
        return "v{}".format(self.var_counter)

    def compile(self, program, name, compile_java=False):
        try:
            ast, context, tcontext = typecheck(program, refined=False)
        except TypeException as t:
            print(t)
            print("Given:")
            print(t.given)
            print("Expected:")
            print(t.expected)
            sys.exit(-1)
        output = generate(ast,
                          context,
                          tcontext,
                          class_name=name,
                          generate_file=True,
                          outputdir=self.outputdir)

        if compile_java:
            compilation = "javac -Xdiags:verbose -cp AeminiumRuntime.jar:. {}.java".format(
                name)
            subprocess.call(compilation, cwd=self.outputdir, shell=True)

    def run_and_retrieve_fitness(self, program):
        try:
            self.compile(program, 'Candidate')

            compilation = "javac -Xdiags:verbose -cp AeminiumRuntime.jar:. Candidate.java"
            ce = subprocess.run(compilation, cwd=self.outputdir, shell=True)
            if ce.returncode != 0:
                subprocess.run("cp Candidate.java CandidateError.java",
                               cwd=self.outputdir,
                               shell=True)
                print("Failed to compile")
                print(program)
                return MAX_DOUBLE

            if not self.compiled_evaluator:
                self.compiled_evaluator = True
                compilation = "javac -Xdiags:verbose -cp AeminiumRuntime.jar:. FitnessEvaluator.java"
                subprocess.call(compilation, cwd=self.outputdir, shell=True)

            program = "java -cp AeminiumRuntime.jar:. FitnessEvaluator".split(
                " ")
            a = subprocess.check_output(program,
                                        cwd=self.outputdir,
                                        timeout=TIMEOUT_RUN).strip()
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
                Node('*', Node('literal', 1.0, type=t_f_c()),
                     Node('-', cond.nodes[0], cond.nodes[1]))
            ])
        else:
            fitness_calc = Node('invocation', 'J.iif', [
                cond,
                Node('lambda', [], Node('literal', 0.0, type=t_f_c())),
                Node('lambda', [], Node('literal', 1.0, type=t_f_c()))
            ])

        main_b = Node('invocation', 'GP.addFitness',
                      [Node('literal', i, type=t_i_c()), fitness_calc])

        argnodes = [
            Node('argument', "__argument_{}".format(i), t)
            for i, t in enumerate(ft.lambda_parameters)
        ]
        argnodes.append(Node('argument', "__return_0", ft.type))

        fn_cond = Node('decl', 'test{}'.format(i), argnodes,
                       Node('argument', '_', t_v), None, None, None,
                       Node('block', main_b))
        return fn_cond

    def depends_on_indices(self, c, middle="__index__"):
        if type(c) == list:
            return any([self.depends_on_indices(n, middle) for n in c])
        if type(c) != Node:
            return False
        if c.nodet in ['atom']:
            if middle in c.nodes[0]:
                return True
            else:
                return False
        else:
            status = any([self.depends_on_indices(n, middle) for n in c.nodes])
        return status

    def prepare_arguments(self, types, tests, counter=0):

        if not types:
            lambda_do_body = Node('block', *tests)
            return Node(
                'invocation',
                'GP.genTests',
                [
                    Node('literal', QUICKCHECK_SIZE, type=t_i_c()),  #size
                    Node('lambda', [], lambda_do_body)
                ])

        t = types.pop(0)
        if t.conditions:
            conditions_to_consider = [
                c for c in t.conditions if not self.depends_on_indices(c)
            ]
        else:
            conditions_to_consider = []

        if len(conditions_to_consider) > 1:
            cs = [c for c in t.conditions if not self.depends_on_indices(c)]
            lambda_cond_body = reduce(lambda x, y: Node('&&', x, y), cs)
        elif len(conditions_to_consider) == 1:
            lambda_cond_body = t.conditions[0]
        else:
            lambda_cond_body = Node('literal', True, type=t_b_c())

        if types:
            lambda_do_body = self.prepare_arguments(types, tests, counter + 1)
        else:
            lambda_do_body = Node('block', *tests)

        # TODO: Verificar se assim se encontra correto:
        # TODO: Falta o t_d
        if t == t_i:
            return Node(
                'invocation',
                'GP.genInteger',
                [
                    Node('literal', QUICKCHECK_SIZE, type=t_i_c()),  #size
                    Node('literal', self.random.randint(0, 1000),
                         type=t_i_c()),  #seed
                    Node('lambda', [('__return_0', t.type)], lambda_cond_body),
                    Node('lambda', [('__argument_{}'.format(counter), t)],
                         lambda_do_body)
                ])
        elif t == t_b:
            return Node(
                'invocation',
                'GP.genBoolean',
                [
                    Node('literal', QUICKCHECK_SIZE, type=t_i_c()),  #size
                    Node('literal', self.random.randint(0, 1000),
                         type=t_i_c()),  #seed
                    Node('lambda', [('__return_0', t.type)], lambda_cond_body),
                    Node('lambda', [('__argument_{}'.format(counter), t)],
                         lambda_do_body)
                ])
        elif t == t_s:
            return Node(
                'invocation',
                'GP.genString',
                [
                    Node('literal', QUICKCHECK_SIZE, type=t_i_c()),  #size
                    Node('literal', self.random.randint(0, 1000),
                         type=t_i_c()),  #seed
                    Node('lambda', [('__return_0', t.type)], lambda_cond_body),
                    Node('lambda', [('__argument_{}'.format(counter), t)],
                         lambda_do_body)
                ])
        elif t == t_f:
            # TODO: Verificar isto, confusao entre genFloat e genDouble
            return Node(
                'invocation',
                'GP.genFloat',
                [
                    Node('literal', QUICKCHECK_SIZE, type=t_i_c()),  #size
                    Node('literal', self.random.randint(0, 1000),
                         type=t_i_c()),  #seed
                    Node('lambda', [('__return_0', t.type)], lambda_cond_body),
                    Node('lambda', [('__argument_{}'.format(counter), t)],
                         lambda_do_body)
                ])
        else:
            return Node(
                'invocation',
                'GP.genObject',
                [
                    Node('literal', QUICKCHECK_SIZE, type=t_i_c()),  #size
                    self.random_ast(t, constructors_only=True,
                                    no_vars=True),  #object
                    Node('lambda', [('__return_0', t)], lambda_cond_body),
                    Node('lambda', [('__argument_{}'.format(counter), t)],
                         lambda_do_body)
                ])

    def create_evaluator_program(self, fname, ftype):

        dependencies = [
            nat for nat in self.root if nat.nodet in ['native', 'type']
        ]

        tests = [
            self.compile_condition(i, cond, ftype)
            for i, cond in enumerate(ftype.conditions)
        ]

        args = [
            Node('atom', '__argument_{}'.format(i))
            for i, v in enumerate(ftype.lambda_parameters)
        ]

        call = Node('let',
                    '__return_0',
                    Node('invocation', "Candidate.{}".format(fname), args),
                    ftype.type,
                    coerced=False)
        tests_to_do = [
            Node('invocation', 'test{}'.format(i),
                 [a for a in args] + [Node('atom', '__return_0')])
            for i, cond in enumerate(ftype.conditions) if tests[i]
        ]
        tests = [t for t in tests if t]

        fn_targets = []
        for decl in [c for c in self.root if c.nodet == 'decl']:
            fn_target = copy.deepcopy(decl)
            fn_target.nodet = 'native'
            fn_target.nodes = list(fn_target.nodes)[:-1]
            fn_target.nodes[0] = 'Candidate.{}'.format(decl.nodes[0])
            fn_targets.append(fn_target)

        variableIterator = self.prepare_arguments(
            copy.deepcopy(ftype.lambda_parameters), [call] + tests_to_do)

        main_b = [variableIterator] + [
            Node('invocation', 'System.out.println',
                 [Node('invocation', 'GP.getFitness', [])])
        ]

        fn_main = Node('decl', 'main', [
            Node('argument', 'args', Type('Array', type_arguments=['String']))
        ], Node('argument', '_', Type('Void')), None, None, None,
                       Node('block', *main_b))

        n = native.parse_strict
        fn_genInteger = n(
            "native GP.genInteger : (_:Integer, _:Integer, _:(Integer) -> Boolean, _:(Integer) -> Void) -> _:Void"
        )
        fn_genDouble = n(
            "native GP.genDouble : (_:Integer, _:Integer, _:(Double) -> Boolean, _:(Double) -> Void) -> _:Void"
        )
        fn_genBoolean = n(
            "native GP.genBoolean : (_:Integer, _:Integer, _:(Boolean) -> Boolean, _:(Boolean) -> Void) -> _:Void"
        )
        fn_genFloat = n(
            "native GP.genFloat : (_:Integer, _:Integer, _:(Float) -> Boolean, _:(Float) -> Void) -> _:Void"
        )
        fn_genString = n(
            "native GP.genString : (_:Integer, _:Integer, _:(String) -> Boolean, _:(String) -> Void) -> _:Void"
        )
        fn_genObject = n(
            "native GP.genObject : T => (_:Integer, _:T, _:(T) -> Boolean, _:(T) -> Void) -> _:Void"
        )
        fn_genTests = n(
            "native GP.genTests : (_:Integer, _:() -> Void) -> _:Void")
        fn_out = n("native System.out.println : (_:Double) -> _:Void")
        fn_addFitness = n(
            "native GP.addFitness : (_:Integer, _:Double) -> _:Double")
        fn_getFitness = n("native GP.getFitness : () -> _:Double")
        fn_if = n(
            "native J.iif : T => (_:Boolean, _: () -> T, _:() -> T) -> _:T")
        fn_abs = n("native Math.abs : T => (_:Double) -> _:Double")
        helpers = [fn_if, fn_abs]
        p = dependencies + helpers + fn_targets + [
            fn_genInteger, fn_genBoolean, fn_genDouble, fn_genFloat,
            fn_genString, fn_genObject, fn_genTests, fn_getFitness,
            fn_addFitness, fn_out, fn_if
        ] + tests + [fn_main]

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

    def random_ast(self,
                   tp,
                   depth=0,
                   max_depth=MAX_DEPTH,
                   constructors_only=False,
                   full=False,
                   no_vars=False):
        if depth >= max_depth:
            constructors_only = True
        if depth > max_depth:
            raise MaxDepthException("Max depth exceeded!")

        is_present = any([tp == t for t in self.typechecker.typecontext.types])
        if not is_present and tp.lambda_parameters == None:
            # This is a generic type, replace with Integer:
            tp = t_i.copy()

        def random_int_literal(tp, **kwargs):
            def wrap(v):
                if v > MAX_INT:
                    return MAX_INT
                if v < MIN_INT:
                    return MIN_INT
                return v

            v = wrap(int(random.gauss(0, (MAX_INT - MIN_INT) / 3.0)))
            if tp.conditions and self.refined:
                key = str(tp)
                if key in self.cached_z3_random:
                    options = self.cached_z3_random[key]
                else:
                    options = zed.generate_random_type(tp, MAX_TRIES_Z3)
                    self.cached_z3_random[key] = options
                if options:
                    v = random.choice(options)
                    if v == None:
                        return None
                    v = v.as_long()
            return Node('literal', v, type=t_i_c())

        def random_boolean_literal(tp, **kwargs):
            v = random.choice([True, False])
            return Node('literal', v, type=t_b_c())

        def random_double_literal(tp, **kwargs):
            v = random.gauss(0, (MAX_DOUBLE - MIN_DOUBLE) / 3.0)
            return Node('literal', v, type=t_f_c())

        def random_string_literal(tp, **kwargs):
            length = random.randint(1, 20)
            letters = 'abcdefghijklmnopqrstuvwxyz'
            string = ''.join(random.choice(letters) for i in range(length))
            return Node('literal', string, type=t_s)  #TODO

        def random_let(tp, **kwargs):
            var_name = "var_{}".format(random.randint(0, 1000000))

            random_type = self.random.choice(
                self.typechecker.typecontext.types)

            df = self.random_ast(random_type, depth + 1, max_depth=max_depth)
            l = Node('let', var_name, df, coerced=False)
            self.context.push_frame()
            self.context.set(var_name, random_type)
            u = self.random_ast(tp, depth + 1, max_depth=max_depth)
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

        def random_invocation(tp, no_args=False, level=0, **kwargs):
            options = []
            for decl in self.context.stack[0]:
                decl_t = self.context.stack[0][decl]
                if self.typechecker.is_subtype(decl_t.type,
                                               tp):  # TODO generic
                    if no_args or constructors_only:
                        if decl_t.lambda_parameters != []:
                            continue
                    if decl != self.function_name:
                        if decl_t.binders:
                            # Handle generic return type
                            decl_t = self.typechecker.unify(decl_t,
                                                            return_type=tp)
                            # TODO - generate other types
                        options.append((decl, decl_t))

            if not options:
                if level == 0:
                    return random_invocation(tp,
                                             no_args=False,
                                             level=1,
                                             **kwargs)
                else:
                    return None

            if options:
                f, ft = random.choice(options)
                try:
                    args = [
                        self.random_ast(at, depth + 1, max_depth=max_depth)
                        for at in ft.lambda_parameters
                    ]
                    if all(args):
                        n = Node('invocation', f, args)
                        try:
                            self.typechecker.typecheck(n, expects=tp)
                            return n
                        except TypeException:
                            return None
                except MaxDepthException:
                    print("failed depth")
                    return None
            else:
                print("no options")
                return None

        def random_operator(tp, **kwargs):
            if any([tp == t for t in [t_i, t_f]]):
                op = self.random.choice(['+', '-', '*', '/', '%'])
                t_a = tp == t_i and t_i_c() or self.random.choice(
                    [t_i_c(), t_f_c()])
                a1 = self.random_ast(t_a, depth + 1, max_depth=max_depth)
                if op == '/':
                    if t_a == t_i:
                        t_a.add_condition(expr.parse_strict('__return_0 != 0'))
                    if t_a == t_f:
                        t_a.add_condition(
                            expr.parse_strict('__return_0 != 0.0'))
                a2 = self.random_ast(t_a, depth + 1, max_depth=max_depth)
                return Node(op, a1, a2)
            elif tp == t_b:
                a1 = self.random_ast(t_b, depth + 1, max_depth=max_depth)
                a2 = self.random_ast(t_b, depth + 1, max_depth=max_depth)
                return Node(self.random.choice(['&&', '||']), a1, a2)
            else:
                return None

        def random_lambda(tp, **kwargs):
            return Node(
                'lambda', [
                    Node('argument', self.next_var(), t)
                    for t in tp.lambda_parameters
                ], self.random_ast(tp.type, depth + 1, max_depth=max_depth))

        possible_generators = []

        if tp.lambda_parameters != None:
            possible_generators.append(random_lambda)
        else:

            if tp == t_i:
                possible_generators.append(random_int_literal)
            if tp == t_b:
                possible_generators.append(random_boolean_literal)
            if tp == t_f:
                possible_generators.append(random_double_literal)
            if tp == t_s:
                possible_generators.append(random_string_literal)

            if self.context.variables() and not no_vars:
                possible_generators.append(random_atom)

            if constructors_only:
                possible_generators.append(random_invocation)
                k = None
                for i in range(N_TRIES_REFINEMENT_CHECK):
                    k = random.choice(possible_generators)(tp, no_args=True)
                    if k:
                        return k
                return None

            possible_generators.append(random_invocation)
            #possible_generators.append(random_operator)

        if depth >= max_depth:
            if possible_generators:
                k = random.choice(possible_generators)(tp, no_args=False)
            else:
                print("Could not finish ", tp)

        if not possible_generators:
            raise NoPossibleExpressionException(
                "Could not generate random code for type {}.".format(tp))
        k = None
        i = 0
        while not k:
            try:
                k = random.choice(possible_generators)(tp)
            except GenException as e:
                pass
                print("gen error")
            except TypeError as e:
                print("type error error")
                pass
            i += 1
            if i > MAX_TRIES_TO_GEN_CHILD:
                raise Exception(
                    "Could not generate random code for type {}".format(tp))

        return k

    def random_individual(self, max_depth=MAX_DEPTH):
        self.reset_zed()
        for i in range(N_TRIES_REFINEMENT_CHECK):
            try:
                c = self.random_ast(tp=self.type, max_depth=max_depth)
                if c and self.validate(c, expects=self.type):
                    return c
                else:
                    print("Failed to validate", c)
            except Exception as e:
                print(e)
                print("hello")
        raise GenException("Could not generate AST for type {}".format(
            self.type))

    def validate(self, candidate, expects=None):

        f = copy.deepcopy(self.function_template)
        nf = replace_hole(f, candidate)

        program_evaluator = copy.deepcopy(self.program_evaluator)
        program = replace_hole(program_evaluator, candidate)

        try:
            typecheck(program, refined=self.refined)
            return nf
        except TypeException as c:
            # TODO!!!!
            #print(c)
            #print(candidate)
            #print("....")
            return False

    def crossover(self, p1, p2, expected=None):
        self.reset_zed()
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
        self.reset_zed()
        if not expected:
            expected = self.type

        can_be_source = lambda n: type(n) == list or (type(
            n) == Node and hasattr(n, 'type') and n.nodet not in
                                                      ['atom', 'literal'])
        can_be_replaced = lambda n: type(n) == Node and hasattr(n, 'type')
        repeat = lambda x, i: [x for a in range(i)]

        def count_children(n):
            if type(n) == list:
                return sum([count_children(x) for x in n])
            elif can_be_replaced(n):
                return 1 + sum([count_children(x) for x in n.nodes])
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

        indices_to_replace = [('h', i) for i in range(len(list_source))
                              if can_be_replaced(list_source[i])]
        for entry in [
                repeat(('d', i), count_children(list_source[i]))
                for i in range(len(list_source))
                if can_be_source(list_source[i])
        ]:
            indices_to_replace.extend(entry)

        if not indices_to_replace:
            return self.random_ast(expected)

        w, index = random.choice(indices_to_replace)

        if w == 'd':
            if type(c) == list:
                exp = expected[index]
            elif type(c) == Node and c.nodet == 'invocation':
                ft = self.context.find(c.nodes[0])
                exp = ft.lambda_parameters  # first argument is parameter list
            else:
                exp = list_source[index].type
            save(index,
                 self.mutate(list_source[index], source=source, expected=exp))
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

        for i, candidate in enumerate(population):

            hash_s = pp(candidate)
            if hash_s not in self.candidate_map:
                program_evaluator = copy.deepcopy(self.program_evaluator)
                program = replace_hole(program_evaluator, candidate)
                self.candidate_map[hash_s] = self.run_and_retrieve_fitness(
                    program)
            candidate.fitness = self.candidate_map[hash_s]

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
        self.start_time = time.time()
        population = []
        for i in range(POPULATION_SIZE):
            p = self.random_individual(max_depth=i % 15)
            population.append(p)

        for i in range(MAX_GENERATIONS):
            t = (time.time() - self.start_time)
            print("Generation", i, "time:", t)

            self.fitness_evaluator = self.create_evaluator_program(
                self.function_name, self.function_type)
            self.compiled_evaluator = False

            self.evaluate(population)

            old_population = sorted(population, key=lambda x: x.fitness)

            if old_population[0].fitness == 0.0:
                print("FOUND SOLUTION AT GENERATION", i)
                t = (time.time() - self.start_time)
                print("Time:", t)
                return [self.clean(p) for p in old_population[:1]]

            for p in old_population[::-1]:
                print("f:", p.fitness, prettyprint(p))

            offspring = copy.deepcopy(old_population[:ELITISM_SIZE]) + [
                self.random_individual(max_depth=i)
                for i in range(NOVELTY_SIZE)
            ]

            while len(
                    offspring) < POPULATION_SIZE - ELITISM_SIZE - NOVELTY_SIZE:
                parent1 = self.tournament(old_population)
                try:
                    if self.random.random() < PROB_XOVER:
                        parent2 = self.tournament(old_population)
                        child = self.crossover(parent1, parent2)
                    else:
                        child = self.mutate(parent1)

                    if self.validate(child):
                        offspring.append(child)
                    else:
                        raise Exception()
                except Exception as e:
                    #print("Failed to mutate or crossover", e)
                    # TODO!!!!!
                    continue

            population = offspring

        self.evaluate(population)
        return [self.clean(p) for p in population]


def synthesise_with_outputdir(outputdir):
    def synthesise(hole,
                   goal_type,
                   root,
                   context,
                   function_name,
                   function_type,
                   typechecker,
                   rand=None,
                   refined=False):
        s = Synthesiser(hole, goal_type, root, context, function_name,
                        function_type, typechecker, rand, refined, outputdir)
        candidates = s.evolve()

        print("Found {} suitable definitions".format(len(candidates)))
        for approved in candidates:
            print(pp(approved), "[Fitness:", approved.fitness, "]")

        if not candidates:
            raise Exception("Hole unknown")

        return candidates[0]

    return synthesise
