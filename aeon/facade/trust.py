"""Trust report — make the trusted computing base of a program auditable.

Aeon's refinement guarantees are only as strong as the assumptions the type
checker does *not* verify. Two such assumptions are trusted verbatim:

* ``axiom`` declarations — Lean-style trusted constants whose (possibly
  refined) type is assumed and never checked.
* ``native`` bindings whose type carries a non-trivial refinement, e.g.
  ``def abs (i:Int) : {v:Int | v >= 0} := native "abs(i)"`` — the ``v >= 0``
  is *asserted* about an opaque Python string, never proved.

Both desugar to a ``native``-backed body, so we recover them by walking the
core program. This module computes, for a whole program (or for the
transitive dependencies of one function), the frontier of such trusted,
refined definitions — the answer to "what am I trusting when I trust this
proof?". See issue #442.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
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
from aeon.core.types import (
    AbstractionType,
    ExistentialType,
    RefinedType,
    Type,
    TypeConstructor,
    TypePolymorphism,
    RefinementPolymorphism,
    type_free_term_vars,
)
from aeon.utils.location import FileLocation, Location
from aeon.utils.name import Name

# Binder identities are rendered with superscript digits (e.g. ``v¹³⁶``); strip
# them so the report shows source-like names. Only digits appear (ids are ints).
_SUPERSCRIPT_DIGITS = "⁰¹²³⁴⁵⁶⁷⁸⁹"
_STRIP_SUPERSCRIPTS = str.maketrans("", "", _SUPERSCRIPT_DIGITS)


def _clean(s: str) -> str:
    """Strip binder-id superscripts, collapse runs of spaces, and drop the
    stray space the core printer leaves before a closing ``)``/``}``."""
    s = s.translate(_STRIP_SUPERSCRIPTS)
    s = re.sub(r" +", " ", s)
    s = re.sub(r" +([)}])", r"\1", s)
    return s.strip()


def render_type(t: Type) -> str:
    """A source-like rendering of a core type (binder ids stripped)."""
    return _clean(str(t))


def has_nontrivial_refinement(t: Type) -> bool:
    """Whether ``t`` carries a refinement that is not trivially ``true`` — i.e.
    the type asserts something a plain base type (``Int``/``Float``/…) does
    not."""
    match t:
        case RefinedType(_, inner, ref):
            if ref != LiquidLiteralBool(True):
                return True
            return has_nontrivial_refinement(inner)
        case AbstractionType(_, vt, rt):
            return has_nontrivial_refinement(vt) or has_nontrivial_refinement(rt)
        case TypePolymorphism(_, _, body):
            return has_nontrivial_refinement(body)
        case RefinementPolymorphism(_, sort, body):
            return has_nontrivial_refinement(sort) or has_nontrivial_refinement(body)
        case ExistentialType(binders, body):
            return any(has_nontrivial_refinement(bt) for _, bt in binders) or has_nontrivial_refinement(body)
        case TypeConstructor(_, args):
            return any(has_nontrivial_refinement(a) for a in args)
        case _:
            return False


def _peel_to_body(t: Term) -> Term:
    """Strip leading value/type/refinement abstractions and annotations to reach
    the computational body of a definition."""
    while True:
        match t:
            case TypeAbstraction(_, _, body):
                t = body
            case RefinementAbstraction(_, _, body):
                t = body
            case Abstraction(_, body):
                t = body
            case Annotation(expr, _):
                t = expr
            case _:
                return t


def _application_head(t: Term) -> Term:
    """Peel application / type-application / refinement-application spines to the
    head term."""
    while True:
        match t:
            case Application(fun, _):
                t = fun
            case TypeApplication(body, _):
                t = body
            case RefinementApplication(body, _):
                t = body
            case _:
                return t


# The sentinel native code an ``axiom`` desugars to (see parser.axiom_decl).
_AXIOM_SENTINEL = "()"


def _native_code(value: Term) -> str | None:
    """If ``value`` is a ``native``-backed body, return the native code string
    (``""`` when the argument isn't a string literal); otherwise ``None``."""
    body = _peel_to_body(value)
    if not isinstance(body, Application):
        return None
    head = _application_head(body.fun)
    if isinstance(head, Var) and head.name.name in ("native", "native_import"):
        arg = body.arg
        return str(arg.value) if isinstance(arg, Literal) else ""
    return None


def _is_native_import(value: Term) -> bool:
    head = _application_head(_peel_to_body(value))
    return isinstance(head, Var) and head.name.name == "native_import"


def _collect_term_vars(t: Term) -> set[Name]:
    """All ``Var`` names referenced anywhere in ``t`` (used to build the
    top-level dependency graph)."""
    acc: set[Name] = set()

    def go(node: Term) -> None:
        match node:
            case Var(name):
                acc.add(name)
            case Application(fun, arg):
                go(fun)
                go(arg)
            case Abstraction(_, body):
                go(body)
            case Let(_, v, b):
                go(v)
                go(b)
            case Rec(_, _, v, b):
                go(v)
                go(b)
            case If(c, then, otherwise):
                go(c)
                go(then)
                go(otherwise)
            case Annotation(expr, _):
                go(expr)
            case TypeAbstraction(_, _, body):
                go(body)
            case RefinementAbstraction(_, _, body):
                go(body)
            case TypeApplication(body, _):
                go(body)
            case RefinementApplication(body, refinement):
                go(body)
                go(refinement)
            case _:
                pass

    go(t)
    return acc


def _display_name(name: Name) -> str:
    """Render a core name source-like: a ``Module_`` prefix (capitalised) is
    shown with dot syntax (``Math_abs`` → ``Math.abs``), preserving any further
    underscores (``Math_floor_division`` → ``Math.floor_division``)."""
    raw = name.name
    m = re.match(r"^([A-Z][A-Za-z0-9]*)_(.+)$", raw)
    return f"{m.group(1)}.{m.group(2)}" if m else raw


def _format_loc(loc: Location) -> str:
    if isinstance(loc, FileLocation):
        line, col = loc.start
        return f"{loc.file}:{line}:{col}"
    return "<builtin>"


@dataclass(frozen=True)
class TrustItem:
    """A single trusted, unverified assumption."""

    name: Name
    display: str
    kind: str  # "axiom" | "native"
    type_str: str
    native_code: str  # "" for axioms
    location: str


@dataclass(frozen=True)
class TrustReport:
    filename: str | None
    scope: str | None  # the function name the report was scoped to, or None
    items: tuple[TrustItem, ...] = field(default_factory=tuple)

    @property
    def axioms(self) -> list[TrustItem]:
        return [i for i in self.items if i.kind == "axiom"]

    @property
    def natives(self) -> list[TrustItem]:
        return [i for i in self.items if i.kind == "native"]


@dataclass(frozen=True)
class _Def:
    name: Name
    type: Type | None
    value: Term
    loc: Location


def _top_level_defs(core: Term) -> list[_Def]:
    """The top-level definitions in source order (the ``Rec``/``Let`` spine)."""
    out: list[_Def] = []
    t = core
    while isinstance(t, (Rec, Let)):
        if isinstance(t, Rec):
            out.append(_Def(t.var_name, t.var_type, t.var_value, t.loc))
        else:
            out.append(_Def(t.var_name, None, t.var_value, t.loc))
        t = t.body
    return out


def _reachable(defs: list[_Def], roots: set[Name]) -> set[Name]:
    """Transitive closure of the top-level dependency graph from ``roots``."""
    by_name = {d.name: d for d in defs}
    top_level = set(by_name)
    seen: set[Name] = set()
    stack = [r for r in roots if r in by_name]
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        d = by_name[cur]
        deps = _collect_term_vars(d.value)
        if d.type is not None:
            deps |= set(type_free_term_vars(d.type))
        for dep in deps & top_level:
            if dep not in seen:
                stack.append(dep)
    return seen


def compute_trust_report(core: Term, filename: str | None = None, for_func: str | None = None) -> TrustReport:
    """Collect the axioms and refined ``native`` bindings a program — or, when
    ``for_func`` is given, the transitive dependencies of that function —
    depends on."""
    defs = _top_level_defs(core)

    if for_func is not None:
        target = for_func.replace(".", "_")
        roots = {d.name for d in defs if d.name.name == for_func or d.name.name == target}
        keep = _reachable(defs, roots)
    else:
        keep = {d.name for d in defs}

    items: list[TrustItem] = []
    for d in defs:
        if d.name not in keep:
            continue
        if _is_native_import(d.value):
            continue  # module imports (`native_import`) assert no refinement
        code = _native_code(d.value)
        if code is None:
            continue  # not native-backed → verified the normal way
        is_axiom = code == _AXIOM_SENTINEL
        refined = d.type is not None and has_nontrivial_refinement(d.type)
        # Axioms are always trust-bearing; plain (unrefined) natives are not.
        if not is_axiom and not refined:
            continue
        items.append(
            TrustItem(
                name=d.name,
                display=_display_name(d.name),
                kind="axiom" if is_axiom else "native",
                type_str=render_type(d.type) if d.type is not None else "?",
                native_code="" if is_axiom else code,
                location=_format_loc(d.loc),
            )
        )

    items.sort(key=lambda i: (i.kind, i.display))
    return TrustReport(filename=filename, scope=for_func, items=tuple(items))


def render_report(report: TrustReport) -> str:
    """A human-readable rendering of a :class:`TrustReport`."""
    lines: list[str] = []
    header = "Trust report"
    if report.filename:
        header += f" — {report.filename}"
    lines.append(header)
    if report.scope is not None:
        lines.append(f"(reachable from `{report.scope}`)")
    lines.append("")

    n = len(report.items)
    if n == 0:
        lines.append("No axioms or refined native bindings in scope — the verified part of")
        lines.append("this program rests only on the built-in primitives.")
        return "\n".join(lines)

    lines.append(f"The verified guarantees here rest on {n} trusted assumption(s) the type")
    lines.append("checker does NOT verify — their refinements are *assumed*:")

    def block(title: str, items: list[TrustItem], show_code: bool) -> None:
        if not items:
            return
        lines.append("")
        lines.append(f"  {title} ({len(items)}):")
        for it in items:
            lines.append(f"    • {it.display} : {it.type_str}")
            tail = f"native `{it.native_code}`  " if show_code and it.native_code else ""
            lines.append(f"        {tail}at {it.location}")

    block("Axioms", report.axioms, show_code=False)
    block("Refined native bindings", report.natives, show_code=True)

    lines.append("")
    lines.append("Review these when auditing any proof that depends on them.")
    return "\n".join(lines)
