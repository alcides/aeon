"""Type-inhabitation ports: preserve types rather than inventing I/O behavior.

Query variables are skolems (distinct opaque types). This is the monomorphic
inhabitation problem, not a claim to benchmark polymorphic inference itself.
Function-valued container fields get concrete ADTs because Aeon's ordinary
Seq/Pair parameters have base kind. Their functions remain first-class values.
"""

import ast
import json
import re

from .common import identifier


class Types:
    def __init__(self, source):
        self.tokens = re.findall(r'"(?:\\.|[^"\\])*"|->|=>|[A-Za-z_][\w\']*|[^\s]', source) + ["EOF"]
        self.i = 0

    def peek(self):
        return self.tokens[self.i]

    def pop(self, expected=None):
        value = self.peek()
        if expected is not None and expected != value:
            raise ValueError((expected, value, self.tokens[self.i : self.i + 8]))
        self.i += 1
        return value

    def accept(self, token):
        if self.peek() == token:
            self.pop()
            return True
        return False

    def haskell(self):
        def atom():
            if self.accept("["):
                item = self.haskell()
                self.pop("]")
                return ("List", item)
            if self.accept("("):
                items = [self.haskell()]
                while self.accept(","):
                    items.append(self.haskell())
                self.pop(")")
                if len(items) == 1:
                    return items[0]
                result = items[-1]
                for item in reversed(items[:-1]):
                    result = ("Pair", item, result)
                return result
            return self.pop()

        result = atom()
        args = []
        while self.peek() in ("[", "(") or (self.peek() != "EOF" and re.fullmatch(r"[A-Za-z_][\w\']*", self.peek())):
            args.append(atom())
        if args:
            result = (result, *args)
        return ("arrow", result, self.haskell()) if self.accept("->") else result

    def skeleton(self):
        if self.accept("("):
            t = self.skeleton()
            self.pop(")")
            return t
        tag = self.pop()
        if tag == "TFun":
            return ("arrow", self.skeleton(), self.skeleton())
        name = json.loads(self.pop())
        if tag == "TVar":
            return name
        assert tag == "TCons"
        self.pop("[")
        args = []
        while self.peek() != "]":
            args.append(self.skeleton())
            if not self.accept(","):
                break
        self.pop("]")
        return (name, *args) if args else name

    def arguments(self):
        self.pop("[")
        result = []
        while self.peek() != "]":
            self.pop("(")
            name = json.loads(self.pop())
            self.pop(",")
            typ = self.skeleton()
            self.pop(")")
            result.append((name, typ))
            if not self.accept(","):
                break
        self.pop("]")
        self.pop("EOF")
        return result


def contains_function(typ):
    return isinstance(typ, tuple) and (typ[0] == "arrow" or any(contains_function(t) for t in typ[1:]))


class QueryEmitter:
    def __init__(self):
        self.abstract = set()
        self.special = {}

    def typ(self, t):
        if isinstance(t, str):
            if t[0].islower():
                name = "Abstract_" + identifier(t)
                self.abstract.add(name)
                return name
            if t == "Int64":
                return "{v:Int | v >= (0 - 9223372036854775808) && v <= 9223372036854775807}"
            if t == "Char":
                return "Character"
            if t == "String":
                return "(Seq Character)"
            return t
        name, *args = t
        if name == "arrow":
            return f"(x:{self.typ(args[0])}) -> {self.typ(args[1])}"
        if name == "@@hplusTC@@Eq":
            return f"(x:{self.typ(args[0])}) -> (y:{self.typ(args[0])}) -> Bool"
        if name == "@@hplusTC@@Ord":
            return f"(x:{self.typ(args[0])}) -> (y:{self.typ(args[0])}) -> Ordering"
        if any(contains_function(a) for a in args):
            if t not in self.special:
                self.special[t] = f"QueryData{len(self.special) + 1}"
            return self.special[t]
        return "(" + {"List": "Seq"}.get(name, name) + " " + " ".join("(" + self.typ(a) + ")" for a in args) + ")"

    def declarations(self):
        code = []
        done = set()
        while len(done) < len(self.special):
            typ = next(t for t in self.special if t not in done)
            done.add(typ)
            name = self.special[typ]
            tag, *args = typ
            fields = [self.typ(t) for t in args]
            code.append(f"inductive {name}")
            if tag == "List":
                code.extend([f"| nil{name} : {name}", f"| cons{name} (head:{fields[0]}) (tail:{name}) : {name}"])
            elif tag == "Pair":
                code.append(f"| pair{name} (first:{fields[0]}) (second:{fields[1]}) : {name}")
            elif tag == "Maybe":
                code.extend([f"| none{name} : {name}", f"| some{name} (value:{fields[0]}) : {name}"])
            elif tag == "Either":
                code.extend(
                    [f"| left{name} (value:{fields[0]}) : {name}", f"| right{name} (value:{fields[1]}) : {name}"]
                )
            else:
                raise ValueError(tag)
        return "\n".join("type " + n for n in sorted(self.abstract)) + "\n" + "\n".join(code) + "\n"


def program(args, result):
    emitter = QueryEmitter()
    binders = " ".join(f"({identifier(name)}:{emitter.typ(t)})" for name, t in args)
    ret = emitter.typ(result)
    code = "open Seq\nopen Maybe\nopen Pair\nopen Functional\nopen Either\nopen Ordering\nopen Bytes\n"
    # A Character is one code point, not an arbitrary String.
    code += "inductive Character\n| character (codepoint:{v:Int | v >= 0 && v <= 1114111}) : Character\n"
    return (
        code
        + emitter.declarations()
        + f"\n# Type inhabitation is the complete upstream specification.\ndef target {binders} : {ret} := ?hole;\n"
    )


def hoogle(corpus):
    path = corpus.source_root / "hoogle/benchmark/suites/working.yml"
    entries = [
        {"name": m[1].strip(), "query": json.loads(m[2])}
        for m in re.finditer(r'^- name:\s*(.+)\n\s+query:\s*("[^\n]+")', path.read_text(), re.M)
    ]
    assert len(entries) == 44
    for item in entries:
        query = item["query"]
        constraints = []
        if "=>" in query:
            context, query = query.split("=>", 1)
            for index, c in enumerate(context.strip(" ()").split(",")):
                cls, var = c.split()
                assert cls in ("Eq", "Ord")
                constraints.append((f"dictionary{index}", ("@@hplusTC@@" + cls, var)))
        parser = Types(query)
        typ = parser.haskell()
        parser.pop("EOF")
        args = list(constraints)
        while isinstance(typ, tuple) and typ[0] == "arrow":
            args.append((f"arg{len(args)}", typ[1]))
            typ = typ[2]
        corpus.add(
            "hoogle",
            identifier(item["name"]),
            path,
            program(args, typ),
            specification="type-inhabitation",
            original_type=item["query"],
            type_variables="distinct opaque skolems",
        )


def hectare(corpus):
    path = corpus.source_root / "hectare/scripts/run_tests.py"
    tree = ast.parse(path.read_text())
    for assignment in tree.body:
        if not isinstance(assignment, ast.Assign) or not isinstance(assignment.value, ast.List):
            continue
        for call in assignment.value.elts:
            if not isinstance(call, ast.Call) or not isinstance(call.func, ast.Name) or call.func.id != "Benchmark":
                continue
            name, size, _solution, arguments, result = [ast.literal_eval(x) for x in call.args]
            args = Types(arguments).arguments()
            parser = Types(result)
            typ = parser.skeleton()
            parser.pop("EOF")
            group = assignment.targets[0].id
            corpus.add(
                "hectare/" + group,
                identifier(name),
                path,
                program(args, typ),
                specification="type-inhabitation",
                original_arguments=arguments,
                original_result=result,
                original_solution_size=size,
                type_variables="distinct opaque skolems",
            )
