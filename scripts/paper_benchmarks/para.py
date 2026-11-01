"""Regenerate deterministic PBE cases from Para's executable specifications.

The public source mirror omits examples.lisp/tests.lisp. A small interpreter
evaluates only the pure Lisp forms in benchmark.lisp; it never executes Lisp,
shell commands, reader macros, file I/O, or arbitrary Python from the artifact.
"""

import math
import random
import re
from dataclasses import dataclass
from functools import reduce

from .common import Group, identifier, sexprs


@dataclass(frozen=True)
class Cons:
    head: object
    tail: object


def linked(items, tail=None):
    for item in reversed(list(items)):
        tail = Cons(item, tail)
    return tail


def sequence(value):
    items = []
    while isinstance(value, Cons):
        items.append(value.head)
        value = value.tail
    if value is not None:
        raise ValueError("Expected a proper list")
    return items


def truth(value):
    return value is not None and value is not False


def car(value):
    return value.head if isinstance(value, Cons) else None


def cdr(value):
    return value.tail if isinstance(value, Cons) else None


def definitions(source, kind):
    source = re.sub(r";[^\n]*", "", source)
    result = []
    for match in re.finditer(r"\(" + kind + r"\s+", source):
        if source[: match.start()].rstrip().endswith("#+nil"):
            continue
        depth = 0
        for end in range(match.start(), len(source)):
            if source[end] == "(":
                depth += 1
            if source[end] == ")":
                depth -= 1
            if depth == 0:
                form = source[match.start() : end + 1].replace("#'", "")
                result.append(sexprs(form)[0].items)
                break
    return result


class Interpreter:
    def __init__(self, source):
        self.functions = {
            "+": lambda *xs: sum(xs),
            "*": lambda *xs: math.prod(xs),
            "-": lambda x, *ys: x - sum(ys) if ys else -x,
            "1+": lambda x: x + 1,
            "1-": lambda x: x - 1,
            "=": lambda x, y: x == y,
            "eq": lambda x, y: x == y,
            ">": lambda x, y: x > y,
            "<": lambda x, y: x < y,
            "max": max,
            "min": min,
            "gcd": math.gcd,
            "expt": pow,
            "floor": lambda x, y: x // y,
            "zerop": lambda x: x == 0,
            "oddp": lambda x: x % 2 != 0,
            "evenp": lambda x: x % 2 == 0,
            "identity": lambda x: x,
            "not": lambda x: not truth(x),
            "consp": lambda x: isinstance(x, Cons),
            "car": car,
            "cdr": cdr,
            "cadr": lambda x: car(cdr(x)),
            "cddr": lambda x: cdr(cdr(x)),
            "cons": Cons,
            "list": lambda *xs: linked(xs),
            "list*": lambda *xs: linked(xs[:-1], xs[-1]),
            "length": lambda x: len(sequence(x)),
            "reverse": lambda x: linked(reversed(sequence(x))),
            "append": lambda *xs: linked([v for x in xs for v in sequence(x)]),
            "nthcdr": lambda n, x: linked(sequence(x)[n:]),
            "nth": lambda n, x: sequence(x)[n] if n < len(sequence(x)) else None,
            "last": lambda x: linked(sequence(x)[-1:]),
            "mapcar": lambda f, x: linked(f(v) for v in sequence(x)),
            "mapcan": lambda f, x: linked(v for y in sequence(x) for v in sequence(f(y))),
            "remove-if-not": lambda f, x: linked(v for v in sequence(x) if truth(f(v))),
            "remove-if": lambda f, x: linked(v for v in sequence(x) if not truth(f(v))),
            "funcall": lambda f, *xs: f(*xs),
            "apply": lambda f, x: f(*sequence(x)),
        }
        for _, name, params, *body in definitions(source, "defun"):
            self.functions[name] = self.function(params.items, body[-1], {})

    def function(self, params, body, env, recursive=False):
        def call(*args):
            local = {**env, **dict(zip(params, args, strict=True))}
            if recursive:
                local["recurse"] = call
            return self.evaluate(body, local)

        return call

    def evaluate(self, node, env):
        if isinstance(node, int):
            return node
        if isinstance(node, str):
            if node == "nil":
                return None
            if node == "t":
                return True
            if node.startswith(":"):
                return node
            return env[node] if node in env else self.functions[node.removeprefix("cl:")]
        op, *args = node.items
        if op == "if":
            return self.evaluate(args[1] if truth(self.evaluate(args[0], env)) else args[2], env)
        if op == "cond":
            for branch in args:
                if truth(self.evaluate(branch.items[0], env)):
                    return self.evaluate(branch.items[-1], env)
            return None
        if op in ("and", "or"):
            result = True if op == "and" else None
            for arg in args:
                result = self.evaluate(arg, env)
                if truth(result) == (op == "or"):
                    break
            return result
        if op == "lambda":
            return self.function(args[0].items, args[-1], env)
        if op == "labels":
            local = dict(env)
            for name, params, *body in (x.items for x in args[0].items):
                local[name] = self.function(params.items, body[-1], local)
            return self.evaluate(args[-1], local)
        if op == "loop":
            # The only loop is the unused count-nonnil helper; retain its pure meaning.
            assert args[:3] == ["for", "x", "in"] and args[4:] == ["when", "x", "sum", 1]
            return sum(truth(x) for x in sequence(self.evaluate(args[3], env)))
        if op == "reduce":
            function = self.evaluate(args[0], env)
            items = sequence(self.evaluate(args[1], env))
            options = {args[i]: self.evaluate(args[i + 1], env) for i in range(2, len(args), 2)}
            if options.get(":from-end"):
                return reduce(lambda acc, x: function(x, acc), reversed(items), options.get(":initial-value", 0))
            return reduce(function, items, options.get(":initial-value", 0))
        function = env[op] if op in env else self.functions[op.removeprefix("cl:")]
        return function(*(self.evaluate(arg, env) for arg in args))


def unpack_type(typ):
    return typ.items if isinstance(typ, Group) else typ


def ae_type(typ):
    t = unpack_type(typ)
    if isinstance(t, str):
        return {"fixnum": "Int", "boolean": "Bool"}[t]
    tag, *args = t
    if tag == "function":
        result = ae_type(args[1])
        for a in reversed(args[0].items):
            result = f"(x:{ae_type(a)}) -> {result}"
        return result
    return (
        "("
        + {"list-of": "Seq", "tree-of": "BinaryTree", "tree-1-of": "LeafTree", "cons": "Pair"}[tag]
        + " "
        + " ".join(ae_type(x) for x in args)
        + ")"
    )


FUNCTIONS = {
    "inc": ("Int -> Int", "fun x => x + 1"),
    "div2": ("Int -> Int", 'fun x => native "x // 2"'),
    "zero": ("Int -> Int", "fun x => 0"),
    "evenp": ("Int -> Bool", "fun x => x % 2 = 0"),
    "nzp": ("Int -> Bool", "fun x => x != 0"),
    "+": ("Int -> Int -> Int", "fun x => fun y => x + y"),
    "count-odd": ("Int -> Int -> Int", "fun x => fun y => if y % 2 != 0 then x + 1 else x"),
}


def function_choices(typ):
    t = typ.items
    args = t[1].items
    result = t[2]
    return (
        ["+", "count-odd"] if len(args) == 2 else ["evenp", "nzp"] if result == "boolean" else ["inc", "div2", "zero"]
    )


def generate(typ, rng, depth=0):
    t = unpack_type(typ)
    if t == "fixnum":
        return rng.randrange(7)
    if t == "boolean":
        return bool(rng.randrange(2))
    tag, *args = t
    if tag == "function":
        return rng.choice(function_choices(typ))
    if tag == "list-of":
        return linked(generate(args[0], rng, depth + 1) for _ in range(rng.randrange(4 if depth else 6)))
    if tag == "cons":
        return Cons(*(generate(t, rng, depth + 1) for t in args))
    if depth >= 3 or rng.randrange(3) == 0:
        return None if tag == "tree-of" else generate(args[0], rng, depth + 1)
    return Cons(generate(args[0], rng, depth + 1), Cons(generate(typ, rng, depth + 1), generate(typ, rng, depth + 1)))


def literal(value, typ):
    t = unpack_type(typ)
    if t == "fixnum":
        return str(value) if value >= 0 else f"(0 - {-value})"
    if t == "boolean":
        return str(truth(value)).lower()
    tag, *args = t
    if tag == "function":
        return "input_" + identifier(value)
    if tag == "list-of":
        result = f"(Seq.nil{{{ae_type(args[0])}}})"
        for x in reversed(sequence(value)):
            result = f"(Seq.cons {literal(x, args[0])} {result})"
        return result
    if tag == "cons":
        return f"(Pair.mk {literal(value.head, args[0])} {literal(value.tail, args[1])})"
    module = "BinaryTree" if tag == "tree-of" else "LeafTree"
    if not isinstance(value, Cons):
        return (
            f"({module}.leaf{{{ae_type(args[0])}}})"
            if tag == "tree-of"
            else f"({module}.leaf {literal(value, args[0])})"
        )
    return f"({module}.node {literal(car(cdr(value)), typ)} {literal(car(value), args[0])} {literal(cdr(cdr(value)), typ)})"


def para(corpus):
    path = corpus.source_root / "para/benchmark.lisp"
    source = path.read_text()
    interpreter = Interpreter(source)
    for index, (_, name, types, result, params, *body) in enumerate(definitions(source, "defproblem")):
        function = interpreter.function(params.items, body[-1], {}, recursive=True)
        rng = random.Random(639000 + index)
        examples = []
        for _ in range(60):
            inputs = [generate(t, rng) for t in types.items]
            values = [
                interpreter.functions[x] if isinstance(t, Group) and t.items[0] == "function" else x
                for x, t in zip(inputs, types.items, strict=True)
            ]
            output = function(*values)
            examples.append(
                f"@example(target {' '.join(literal(x, t) for x, t in zip(inputs, types.items, strict=True))} = {literal(output, result)})"
            )
        code = "open Seq\nopen Pair\n"
        all_types = str(types) + str(result)
        if "tree-of" in all_types:
            code += "open BinaryTree\n"
        if "tree-1-of" in all_types:
            code += "open LeafTree\n"
        code += "\n"
        for fn, (_, body_text) in FUNCTIONS.items():
            # Use binder syntax rather than Haskell's bare arrows.
            if fn in ("+", "count-odd"):
                typ = "(x:Int) -> (y:Int) -> Int"
            else:
                typ = "(x:Int) -> " + ("Bool" if fn in ("evenp", "nzp") else "Int")
            code += f"def input_{identifier(fn)} : {typ} := {body_text};\n"
        code += "\n" + "\n".join(examples) + "\n"
        code += (
            "def target "
            + " ".join(f"(arg{i}:{ae_type(t)})" for i, t in enumerate(types.items))
            + f" : {ae_type(result)} := ?hole;\n"
        )
        corpus.add(
            "para",
            identifier(name),
            path,
            code,
            specification="regenerated-examples",
            examples=len(examples),
            seed=639000 + index,
            original_name=name,
            original_examples_available=False,
            source_mirror="nicolas-abril/para-artifact",
        )
