"""Extract finite qualifier sets (Q) from typing context and types.

Used for predicate abstraction / constrained Horn solving: unknown refinements
are searched as boolean combinations of atoms drawn from Q (see e.g. Jhala &
Vazou, "Refinement Types: A Tutorial", arXiv:2010.07763; Polikarpova et al.,
PLDI 2016 Synquid).
"""

from __future__ import annotations

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidTerm, LiquidVar
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
            for predicate in ty.refinements:
                sink.update(_atoms_from_predicate(predicate.body))
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


def set_membership_atoms(ctx: TypingContext) -> set[LiquidTerm]:
    """One ``mem`` template per set-valued measure, at bound element variables.

    The element and the measured container are variables in scope. Applications
    are not members of the template, so this is not a product over terms.
    """

    def base_of(ty: Type) -> Type:
        if isinstance(ty, RefinedType):
            return base_of(ty.type)
        if isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
            return base_of(ty.body)
        return ty

    def unary_measure(ty: Type) -> tuple[Type, Type] | None:
        current: Type = ty
        while isinstance(current, (TypePolymorphism, RefinementPolymorphism)):
            current = current.body
        if not isinstance(current, AbstractionType):
            return None
        argument = base_of(current.var_type)
        result = base_of(current.type)
        if isinstance(result, AbstractionType):
            return None
        if not isinstance(result, TypeConstructor) or result.name.name != "Set" or not result.args:
            return None
        return argument, base_of(result.args[0])

    def same(left: Type, right: Type) -> bool:
        left, right = base_of(left), base_of(right)
        if isinstance(left, TypeVar) and isinstance(right, TypeVar):
            return left.name.name == right.name.name
        if isinstance(left, TypeConstructor) and isinstance(right, TypeConstructor):
            return (
                left.name.name == right.name.name
                and len(left.args) == len(right.args)
                and all(same(a, b) for a, b in zip(left.args, right.args))
            )
        return left == right

    variables: list[tuple[Name, Type]] = []
    measures: list[tuple[Name, Type, Type]] = []
    for entry in ctx.entries:
        if isinstance(entry, VariableBinder):
            variables.append((entry.name, base_of(entry.type)))
        if isinstance(entry, (UninterpretedBinder, VariableBinder)):
            shape = unary_measure(entry.type)
            if shape is None or entry.name.name.startswith("Set_"):
                continue
            measures.append((entry.name, shape[0], shape[1]))

    atoms: set[LiquidTerm] = set()
    for measure, container_type, element_type in measures:
        containers = [name for name, ty in variables if same(ty, container_type)]
        elements = [name for name, ty in variables if same(ty, element_type)]
        for container in containers:
            for element in elements:
                atoms.add(
                    LiquidApp(
                        Name("Set_mem", 0),
                        [LiquidVar(element), LiquidApp(measure, [LiquidVar(container)])],
                    )
                )
    return atoms


def extract_qualifier_atoms(
    ctx: TypingContext,
    goal_type: Type | None = None,
    term: Term | None = None,
    *,
    max_atoms: int | None = 512,
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
    sink.update(set_membership_atoms(ctx))
    if max_atoms is None or len(sink) <= max_atoms:
        return frozenset(sink)
    ordered = sorted(sink, key=repr)
    return frozenset(ordered[:max_atoms])
