"""Export Aeon functions with lexical binding identity and strict evaluation.

Core types are erased, functions stay curried, and native Python expressions
receive their source-level lexical namespace. Only reachable definitions are
emitted; native expressions conservatively retain every visible binding.
"""

from __future__ import annotations

from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    Hole,
    If,
    Let,
    Literal,
    Rec,
    RefinementAbstraction,
    RefinementApplication,
    Term,
    TypeAbstraction,
    TypeApplication,
    Var,
)
import keyword
import re

from aeon.optimization.whnf import strip_type_wrappers
from aeon.core.types import t_bool, t_string, t_unit
from aeon.utils.name import Name

# Aeon operators that map onto a Python infix operator. The interpreter
# defines each as a curried lambda in the prelude; here we render the
# saturated application directly as ``(a <op> b)``.
BINARY_OPERATORS: dict[str, str] = {
    "+": "+",
    "-": "-",
    "*": "*",
    "/": "/",
    "%": "%",
    "<": "<",
    ">": ">",
    "<=": "<=",
    ">=": ">=",
    "==": "==",
    "!=": "!=",
    "&&": "and",
    "||": "or",
}


class PythonExportError(Exception):
    """Raised when a term cannot be translated to pure Python."""


def find_binding(core: Term, fun_name: str) -> tuple[Name, Term] | None:
    """Walk the top-level ``Rec``/``Let`` chain and return the
    ``(name, value)`` pair whose source name matches ``fun_name``."""
    t = core
    while isinstance(t, (Rec, Let)):
        if t.var_name.name == fun_name:
            return t.var_name, t.var_value
        t = t.body
    return None


def _unfold_application(t: Application) -> tuple[Term, list[Term]]:
    """Flatten a curried application spine into ``(head, args)`` with the
    type wrappers stripped from the head."""
    args: list[Term] = []
    cur: Term = t
    while isinstance(cur, Application):
        args.append(cur.arg)
        cur = cur.fun
    args.reverse()
    return strip_type_wrappers(cur), args


def _literal_to_python(value: object, type) -> str:
    if type == t_string:
        return repr(value)
    if type == t_bool:
        return "True" if value else "False"
    if type == t_unit or value is None:
        return "None"
    return repr(value)


class _Generator:
    def __init__(self):
        self.names: dict[Name, str] = {}
        self.used = {"_aeon_builtins"}
        self.refs: set[Name] = set()

    def name(self, name: Name) -> str:
        if name not in self.names:
            base = re.sub(r"\W", "_", name.name)
            if not base or base[0].isdigit() or keyword.iskeyword(base):
                base = "_" + base
            candidate, suffix = base, 1
            while candidate in self.used:
                candidate = f"{base}_{suffix}"
                suffix += 1
            self.names[name] = candidate
            self.used.add(candidate)
        return self.names[name]

    def gen(self, t: Term, env: dict[str, Name]) -> str:
        match t:
            case Literal(value, ty):
                return _literal_to_python(value, ty)
            case Var(name):
                self.refs.add(name)
                return self.name(name)
            case Annotation(expr, _):
                return self.gen(expr, env)
            case TypeAbstraction(_, _, body) | RefinementAbstraction(_, _, body):
                return self.gen(body, env)
            case TypeApplication(body, _) | RefinementApplication(body, _):
                return self.gen(body, env)
            case Abstraction(name, body):
                parameter = self.name(name)
                return f"(lambda {parameter}: {self.gen(body, env | {name.name: name})})"
            case If(cond, then, otherwise):
                return f"({self.gen(then, env)} if {self.gen(cond, env)} else {self.gen(otherwise, env)})"
            case Let(name, value, body):
                parameter = self.name(name)
                return f"(lambda {parameter}: {self.gen(body, env | {name.name: name})})({self.gen(value, env)})"
            case Application():
                return self.application(t, env)
            case Hole(name):
                raise PythonExportError(f"cannot export a function with an unfilled hole: ?{name}")
            case Rec(name, _, _, _, _, _, _):
                raise PythonExportError(
                    f"cannot export local recursive binding '{name.name}'; only top-level functions are supported"
                )
            case _:
                raise PythonExportError(f"unsupported term in export: {type(t).__name__}")

    def application(self, t: Application, env: dict[str, Name]) -> str:
        head, args = _unfold_application(t)
        # Match builtin identity, never a user's binding with the same spelling.
        if isinstance(head, Var) and head.name == Name(head.name.name, 0):
            op = head.name.name
            first = strip_type_wrappers(args[0]) if args else None
            if op == "native" and isinstance(first, Literal):
                # Native expressions can inspect their namespace dynamically.
                # Preserve all lexical dependencies, including those invisible
                # to Aeon's Var traversal. Python lambdas keep this namespace.
                self.refs.update(env.values())
                namespace = ", ".join(f"{key!r}: {self.name(value)}" for key, value in env.items())
                return f"_aeon_builtins.eval({first.value!r}, {{{namespace}}})"
            if op == "native_import" and isinstance(first, Literal):
                return f"_aeon_builtins.__import__({first.value!r})"
            if op == "print" and len(args) == 1:
                return f"(_aeon_builtins.print(_aeon_builtins.str({self.gen(args[0], env)})) or 0)"
            if op == "!" and len(args) == 1:
                return f"(not {self.gen(args[0], env)})"
            if op == "$" and len(args) == 2:
                return f"({self.gen(args[0], env)})({self.gen(args[1], env)})"
            if len(args) == 2:
                left, right = (self.gen(arg, env) for arg in args)
                if op in {"&&", "||", "-->"}:
                    body = {"&&": "x and y", "||": "x or y", "-->": "(not x) or y"}[op]
                    return f"(lambda x, y: {body})({left}, {right})"
                if op == "/":
                    return (
                        "(lambda x, y: x // y if _aeon_builtins.isinstance(x, _aeon_builtins.int) "
                        "and _aeon_builtins.isinstance(y, _aeon_builtins.int) else x / y)"
                        f"({left}, {right})"
                    )
                if op in BINARY_OPERATORS:
                    return f"({left} {BINARY_OPERATORS[op]} {right})"
        out = self.gen(head, env)
        for arg in args:
            out = f"({out})({self.gen(arg, env)})"
        return out

    def binding(self, name: Name, value: Term, env: dict[str, Name]) -> str:
        # Beta reduction can erase let bindings read only by native strings.
        body = strip_type_wrappers(value)
        params: list[str] = []
        if isinstance(body, Abstraction):
            env = env | {name.name: name}
        while isinstance(body, Abstraction):
            params.append(self.name(body.var_name))
            env = env | {body.var_name.name: body.var_name}
            body = strip_type_wrappers(body.body)
        body_src = self.gen(body, env)
        binding = self.name(name)
        if not params:
            return f"{binding} = {body_src}"
        head, *rest = params
        for parameter in reversed(rest):
            body_src = f"lambda {parameter}: {body_src}"
        return f"def {binding}({head}):\n    return {body_src}"


def gen(t: Term) -> str:
    """Render an expression; builtin calls use the exported builtins namespace."""
    return _Generator().gen(t, {})


def top_level_bindings(core: Term) -> list[tuple[Name, Term]]:
    """Return every top-level ``(name, value)`` binding in source order."""
    out: list[tuple[Name, Term]] = []
    t = core
    while isinstance(t, (Rec, Let)):
        out.append((t.var_name, t.var_value))
        t = t.body
    return out


def _native_import_module(value: Term) -> str | None:
    """If ``value`` is a ``native_import "mod"`` binding, return ``"mod"``."""
    head = value
    if isinstance(head, Application):
        head, args = _unfold_application(head)
        if isinstance(head, Var) and head.name.name == "native_import" and args:
            first = strip_type_wrappers(args[0])
            if isinstance(first, Literal):
                return str(first.value)
    return None


def export_function(core: Term, fun_name: str) -> str:
    """Export the visible binding and its lexical dependencies.

    Native expressions retain their entire visible namespace because Python
    can discover dependencies dynamically (for example through globals()).
    """
    bindings = top_level_bindings(core)
    by_name = dict(bindings)
    target = next((name for name, _ in reversed(bindings) if name.name == fun_name), None)
    if target is None:
        raise PythonExportError(f"no top-level function named '{fun_name}' was found")
    if not fun_name.isidentifier() or keyword.iskeyword(fun_name) or fun_name == "_aeon_builtins":
        raise PythonExportError(f"exported entrypoint is not a supported Python identifier: {fun_name!r}")

    generator = _Generator()
    # Reserve the public name before allocating names for shadowed definitions.
    generator.name(target)
    environments: dict[Name, dict[str, Name]] = {}
    env: dict[str, Name] = {}
    for name, _ in bindings:
        generator.name(name)
        environments[name] = env
        env = env | {name.name: name}

    needed = {target} | {name for name, value in bindings if _native_import_module(value) is not None}
    pending = list(needed)
    rendered: dict[Name, str] = {}
    while pending:
        name = pending.pop()
        generator.refs = set()
        rendered[name] = generator.binding(name, by_name[name], environments[name])
        for dependency in generator.refs & by_name.keys():
            if dependency not in needed:
                needed.add(dependency)
                pending.append(dependency)

    parts = ["import builtins as _aeon_builtins"]
    parts.extend(rendered[name] for name, _ in bindings if name in needed)
    return "\n\n".join(parts) + "\n"
