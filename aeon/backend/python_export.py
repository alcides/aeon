"""Export an Aeon function as a stand-alone, pure-Python definition.

This backs the ``--export=fun_name`` CLI flag. The output bundles
``fun_name`` with every top-level binding it transitively depends on
(unreferenced bindings are dropped, but ``native_import`` bindings are always
kept since ``native`` strings reference the imported modules by name). For
each binding the pipeline is:

1. Locate the top-level binding for ``fun_name`` in the core AST.
2. Reduce its body to weak-head normal form (``whnf``) — this strips the
   type-level wrappers introduced by elaboration (type/refinement
   abstractions and applications, annotations) and beta-reduces any redex
   at the head, exposing the underlying ``Abstraction``.
3. Walk the resulting term and emit Python source, mirroring the choices the
   interpreter (``aeon/backend/evaluator.py``) makes at runtime: curried
   lambdas for abstractions, ternaries for ``if``, immediately-applied
   lambdas for ``let``. ``native`` strings are inlined verbatim, exactly as
   the interpreter would ``eval`` them.

The emitted function preserves Aeon's currying convention, so a binary call
``f a b`` becomes ``f(a)(b)`` and the inlined native strings (which reference
the source-level parameter names) resolve against the surrounding lambdas.
"""

from __future__ import annotations

from aeon.core.substitutions import substitution
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


def whnf(t: Term) -> Term:
    """Reduce ``t`` to weak-head normal form.

    Strips the administrative wrappers elaboration leaves around values
    (annotations, type/refinement abstractions and applications) and
    beta-reduces any redex sitting at the head. Reduction stops as soon as
    the head is a value (an ``Abstraction``, ``Literal``, ...) or a stuck
    application — it never descends into a lambda body.
    """
    while True:
        match t:
            case Annotation(expr, _):
                t = expr
            case TypeAbstraction(_, _, body):
                t = body
            case RefinementAbstraction(_, _, body):
                t = body
            case TypeApplication(body, _):
                t = body
            case RefinementApplication(body, _):
                t = body
            case Application(fun, arg):
                f = whnf(fun)
                if isinstance(f, Abstraction):
                    t = substitution(f.body, arg, f.var_name)
                else:
                    return Application(f, arg, t.loc)
            case _:
                return t


def _strip_type_wrappers(t: Term) -> Term:
    """Peel only the type-level wrappers, exposing the operational head of
    an application spine (e.g. the ``Var`` behind a ``native [a]`` instance)."""
    while True:
        match t:
            case Annotation(expr, _):
                t = expr
            case TypeApplication(body, _):
                t = body
            case RefinementApplication(body, _):
                t = body
            case TypeAbstraction(_, _, body):
                t = body
            case RefinementAbstraction(_, _, body):
                t = body
            case _:
                return t


def _unfold_application(t: Application) -> tuple[Term, list[Term]]:
    """Flatten a curried application spine into ``(head, args)`` with the
    type wrappers stripped from the head."""
    args: list[Term] = []
    cur: Term = t
    while isinstance(cur, Application):
        args.append(cur.arg)
        cur = cur.fun
    args.reverse()
    return _strip_type_wrappers(cur), args


def _literal_to_python(value: object, type) -> str:
    if type == t_string:
        return repr(value)
    if type == t_bool:
        return "True" if value else "False"
    if type == t_unit or value is None:
        return "None"
    return repr(value)


def gen(t: Term) -> str:
    """Translate a core ``Term`` into a pure-Python expression string."""
    match t:
        case Literal(value, ty):
            return _literal_to_python(value, ty)
        case Var(name):
            return name.name
        case Annotation(expr, _):
            return gen(expr)
        case TypeAbstraction(_, _, body) | RefinementAbstraction(_, _, body):
            return gen(body)
        case TypeApplication(body, _) | RefinementApplication(body, _):
            return gen(body)
        case Abstraction(var_name, body):
            return f"(lambda {var_name.name}: {gen(body)})"
        case If(cond, then, otherwise):
            return f"({gen(then)} if {gen(cond)} else {gen(otherwise)})"
        case Let(var_name, var_value, body):
            return f"(lambda {var_name.name}: {gen(body)})({gen(var_value)})"
        case Application():
            return _gen_application(t)
        case Hole(name):
            raise PythonExportError(f"cannot export a function with an unfilled hole: ?{name}")
        case Rec(var_name, _, _, _, _, _, _):
            raise PythonExportError(
                f"cannot export local recursive binding '{var_name.name}'; only top-level functions are supported"
            )
        case _:
            raise PythonExportError(f"unsupported term in export: {type(t).__name__}")


def _gen_application(t: Application) -> str:
    head, args = _unfold_application(t)

    if isinstance(head, Var):
        op = head.name.name
        first = _strip_type_wrappers(args[0]) if args else None
        # Inline ``native "..."`` strings verbatim, as the interpreter evals them.
        if op == "native" and isinstance(first, Literal):
            return f"({first.value})"
        if op == "native_import" and isinstance(first, Literal):
            return f"__import__({first.value!r})"
        # ``print`` mirrors the prelude's ``p``: print and yield 0.
        if op == "print" and len(args) == 1:
            return f"(print(str({gen(args[0])})) or 0)"
        # ``!`` is unary boolean negation.
        if op == "!" and len(args) == 1:
            return f"(not {gen(args[0])})"
        # ``-->`` is logical implication.
        if op == "-->" and len(args) == 2:
            return f"((not {gen(args[0])}) or {gen(args[1])})"
        # ``$`` is application.
        if op == "$" and len(args) == 2:
            return f"({gen(args[0])})({gen(args[1])})"
        if op in BINARY_OPERATORS and len(args) == 2:
            return f"({gen(args[0])} {BINARY_OPERATORS[op]} {gen(args[1])})"

    # Fall back to plain curried application.
    out = gen(head)
    for arg in args:
        out = f"({out})({gen(arg)})"
    return out


def top_level_bindings(core: Term) -> list[tuple[Name, Term]]:
    """Return every top-level ``(name, value)`` binding in source order."""
    out: list[tuple[Name, Term]] = []
    t = core
    while isinstance(t, (Rec, Let)):
        out.append((t.var_name, t.var_value))
        t = t.body
    return out


def _collect_refs(t: Term, acc: set[Name]) -> None:
    """Accumulate the names of every ``Var`` that occurs in ``t``."""
    match t:
        case Var(name):
            acc.add(name)
        case Literal() | Hole():
            return
        case Application(fun, arg):
            _collect_refs(fun, acc)
            _collect_refs(arg, acc)
        case Abstraction(_, body):
            _collect_refs(body, acc)
        case Annotation(expr, _):
            _collect_refs(expr, acc)
        case If(cond, then, otherwise):
            _collect_refs(cond, acc)
            _collect_refs(then, acc)
            _collect_refs(otherwise, acc)
        case Let(_, var_value, body):
            _collect_refs(var_value, acc)
            _collect_refs(body, acc)
        case Rec(_, _, var_value, body):
            _collect_refs(var_value, acc)
            _collect_refs(body, acc)
        case TypeAbstraction(_, _, body) | RefinementAbstraction(_, _, body):
            _collect_refs(body, acc)
        case TypeApplication(body, _) | RefinementApplication(body, _):
            _collect_refs(body, acc)


def _native_import_module(value: Term) -> str | None:
    """If ``value`` is a ``native_import "mod"`` binding, return ``"mod"``."""
    head = value
    if isinstance(head, Application):
        head, args = _unfold_application(head)
        if isinstance(head, Var) and head.name.name == "native_import" and args:
            first = _strip_type_wrappers(args[0])
            if isinstance(first, Literal):
                return str(first.value)
    return None


def _render_binding(name: Name, value: Term) -> str:
    """Render a single top-level binding as Python.

    Functions (terms with leading abstractions) become curried ``def``s;
    value bindings — including ``native_import`` and ``native`` constants —
    become module-level assignments so references resolve to the value
    itself, exactly as the interpreter binds them."""
    body = whnf(value)
    params: list[str] = []
    while isinstance(body, Abstraction):
        params.append(body.var_name.name)
        body = whnf(body.body)
    body_src = gen(body)

    if not params:
        return f"{name.name} = {body_src}"

    head, *rest = params
    inner = body_src
    for p in reversed(rest):
        inner = f"lambda {p}: {inner}"
    return f"def {name.name}({head}):\n    return {inner}"


def export_function(core: Term, fun_name: str) -> str:
    """Produce a pure-Python rendering of ``fun_name`` and its dependencies.

    The output bundles ``fun_name`` together with every top-level binding it
    transitively references, dropping anything unmentioned — except
    ``native_import`` bindings, which are always kept (the ``native`` strings
    that depend on them reference the imported modules by name, invisibly to
    AST-level dependency analysis)."""
    bindings = top_level_bindings(core)
    by_name = {name: value for name, value in bindings}

    target = next((name for name, _ in bindings if name.name == fun_name), None)
    if target is None:
        raise PythonExportError(f"no top-level function named '{fun_name}' was found")

    top_names = set(by_name)

    # Transitive closure of the dependencies reachable from the target.
    needed: set[Name] = {target}
    worklist = [target]
    while worklist:
        refs: set[Name] = set()
        _collect_refs(by_name[worklist.pop()], refs)
        for ref in refs:
            if ref in top_names and ref not in needed:
                needed.add(ref)
                worklist.append(ref)

    # ``native_import`` bindings are always included.
    for name, value in bindings:
        if _native_import_module(value) is not None:
            needed.add(name)

    parts = [_render_binding(name, value) for name, value in bindings if name in needed]
    return "\n\n".join(parts) + "\n"
