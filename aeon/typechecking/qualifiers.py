"""Extract finite qualifier sets (Q) from typing context and types.

Used for predicate abstraction / constrained Horn solving: unknown refinements
are searched as boolean combinations of atoms drawn from Q (see e.g. Jhala &
Vazou, "Refinement Types: A Tutorial", arXiv:2010.07763; Polikarpova et al.,
PLDI 2016 Synquid).
"""

from __future__ import annotations

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidTerm
from aeon.core.terms import Abstraction, Annotation, Application, If, Let, Literal, Rec, RefinementApplication
from aeon.core.terms import Term, TypeAbstraction, TypeApplication, Var
from aeon.core.types import (
    AbstractionType,
    LiquidHornApplication,
    RefinementPolymorphism,
    RefinedType,
    Type,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
    liq_true,
)
from aeon.typechecking.context import (
    TypeBinder,
    TypeConstructorBinder,
    TypingContext,
    UninterpretedBinder,
    VariableBinder,
)
from aeon.utils.name import Name

_AND: Name = Name("&&", 0)


def _flatten_and(p: LiquidTerm) -> list[LiquidTerm]:
    if isinstance(p, LiquidApp) and p.fun == _AND:
        return _flatten_and(p.args[0]) + _flatten_and(p.args[1])
    return [p]


def _atoms_from_predicate(p: LiquidTerm) -> list[LiquidTerm]:
    out: list[LiquidTerm] = []
    for chunk in _flatten_and(p):
        if isinstance(chunk, LiquidHornApplication):
            continue
        if chunk == LiquidLiteralBool(True) or chunk == liq_true:
            continue
        out.append(chunk)
    return out


def _collect_from_type(ty: Type, sink: set[LiquidTerm]) -> None:
    match ty:
        case RefinedType(_, inner, ref):
            for atom in _atoms_from_predicate(ref):
                sink.add(atom)
            _collect_from_type(inner, sink)
        case AbstractionType(_, aty, rty):
            _collect_from_type(aty, sink)
            _collect_from_type(rty, sink)
        case TypePolymorphism(_, _, body):
            _collect_from_type(body, sink)
        case RefinementPolymorphism(_, _, body):
            _collect_from_type(body, sink)
        case TypeConstructor(_, args):
            for arg_ty in args:
                _collect_from_type(arg_ty, sink)
        case TypeVar():
            pass
        case _:
            pass


def _collect_from_term(t: Term, sink: set[LiquidTerm]) -> None:
    match t:
        case Annotation(_, ty):
            _collect_from_type(ty, sink)
            _collect_from_term(t.expr, sink)
        case Application(f, a):
            _collect_from_term(f, sink)
            _collect_from_term(a, sink)
        case Abstraction(_, b):
            _collect_from_term(b, sink)
        case Let(_, v, b):
            _collect_from_term(v, sink)
            _collect_from_term(b, sink)
        case Rec(_, vty, vv, b, _, _):
            _collect_from_type(vty, sink)
            _collect_from_term(vv, sink)
            _collect_from_term(b, sink)
        case If(cond, then, otherwise):
            _collect_from_term(cond, sink)
            _collect_from_term(then, sink)
            _collect_from_term(otherwise, sink)
        case TypeAbstraction(_, _, b):
            _collect_from_term(b, sink)
        case TypeApplication(b, ty):
            _collect_from_term(b, sink)
            _collect_from_type(ty, sink)
        case RefinementApplication(b, _):
            _collect_from_term(b, sink)
        case Literal(type=lit_ty):
            _collect_from_type(lit_ty, sink)
        case Var():
            pass
        case _:
            pass


def extract_qualifier_atoms(
    ctx: TypingContext,
    goal_type: Type | None = None,
    term: Term | None = None,
    *,
    max_atoms: int = 512,
) -> frozenset[LiquidTerm]:
    """Finite set Q of boolean liquid atoms from refinements in scope.

    Sources: variable and uninterpreted bindings in ``ctx``, optional
    ``goal_type``, and optional ``term`` (annotations and nested types).
    If more than ``max_atoms`` are found, the set is truncated deterministically.
    """
    sink: set[LiquidTerm] = set()
    for e in ctx.entries:
        match e:
            case VariableBinder(_, ty) | UninterpretedBinder(_, ty):
                _collect_from_type(ty, sink)
            case TypeBinder() | TypeConstructorBinder():
                pass
            case _:
                pass
    if goal_type is not None:
        _collect_from_type(goal_type, sink)
    if term is not None:
        _collect_from_term(term, sink)
    if len(sink) <= max_atoms:
        return frozenset(sink)
    ordered = sorted(sink, key=repr)
    return frozenset(ordered[:max_atoms])
