from __future__ import annotations

from dataclasses import dataclass

from aeon.core.liquid import LiquidTerm
from aeon.core.substitutions import substitution, substitution_in_type
from aeon.core.terms import Abstraction, Annotation, Application, Hole, If, Literal, Term, TypeApplication, Var
from aeon.core.types import AbstractionType, RefinedType, Type, TypePolymorphism, refined_to_unrefined_type, t_bool
from aeon.synthesis.identification import get_holes
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import synth
from aeon.utils.name import Name


def replace_focal_hole(term: Term, hole_name: Name, replacement: Term) -> Term:
    """Replace the focal ``Hole`` (or its sole ``Annotation`` wrapper) by ``replacement``."""
    match term:
        case Hole(name=n) if n == hole_name:
            return replacement
        case Annotation(expr=Hole(name=n), type=_, loc=aloc) if n == hole_name:
            return replacement
        case Annotation(expr=e, type=ty, loc=aloc):
            return Annotation(replace_focal_hole(e, hole_name, replacement), ty, loc=aloc)
        case Application(fun, arg, loc):
            return Application(
                replace_focal_hole(fun, hole_name, replacement),
                replace_focal_hole(arg, hole_name, replacement),
                loc=loc,
            )
        case Abstraction(v, body, loc):
            return Abstraction(v, replace_focal_hole(body, hole_name, replacement), loc=loc)
        case If(cond, then, otherwise, loc):
            return If(
                replace_focal_hole(cond, hole_name, replacement),
                replace_focal_hole(then, hole_name, replacement),
                replace_focal_hole(otherwise, hole_name, replacement),
                loc=loc,
            )
        case TypeApplication(body, ty, loc):
            return TypeApplication(replace_focal_hole(body, hole_name, replacement), ty, loc=loc)
        case Var(_) | Literal(_, _) | Hole(_):
            return term
        case _:
            raise AssertionError(f"tactics: unsupported term shape in replace_focal_hole: {term}")


def replace_hole_expected_annotation(term: Term, hole_name: Name, new_ty: Type) -> Term:
    """Rewrite the focused hole to use ``new_ty`` in its nearest ``Annotation`` (or add one)."""
    match term:
        case Hole(name=n) if n == hole_name:
            return Annotation(Hole(n, term.loc), new_ty, loc=term.loc)
        case Annotation(expr=Hole(name=n, loc=hloc), type=_, loc=aloc) if n == hole_name:
            return Annotation(Hole(n, hloc), new_ty, loc=aloc)
        case Annotation(expr=e, type=ty, loc=aloc):
            return Annotation(replace_hole_expected_annotation(e, hole_name, new_ty), ty, loc=aloc)
        case Application(fun, arg, loc):
            return Application(
                replace_hole_expected_annotation(fun, hole_name, new_ty),
                replace_hole_expected_annotation(arg, hole_name, new_ty),
                loc=loc,
            )
        case Abstraction(v, body, loc):
            return Abstraction(v, replace_hole_expected_annotation(body, hole_name, new_ty), loc=loc)
        case If(cond, then, otherwise, loc):
            return If(
                replace_hole_expected_annotation(cond, hole_name, new_ty),
                replace_hole_expected_annotation(then, hole_name, new_ty),
                replace_hole_expected_annotation(otherwise, hole_name, new_ty),
                loc=loc,
            )
        case TypeApplication(body, ty, loc):
            return TypeApplication(replace_hole_expected_annotation(body, hole_name, new_ty), ty, loc=loc)
        case Var(_) | Literal(_, _) | Hole(_):
            return term
        case _:
            raise AssertionError(f"tactics: unsupported term shape in replace_hole_expected_annotation: {term}")


def _norm_ty(ty: Type, refined_types: bool) -> Type:
    return ty if refined_types else refined_to_unrefined_type(ty)


@dataclass(frozen=True)
class HoleInfo:
    name: Name
    ctx: TypingContext
    expected: Type
    refinement_name: Name | None = None
    refinement_predicate: LiquidTerm | None = None


def hole_constraint_fields(ty: Type) -> tuple[Name | None, LiquidTerm | None]:
    """Surfaces refinement subject/predicate when ``ty`` is a ``RefinedType``."""
    match ty:
        case RefinedType(name, _, ref):
            return name, ref
        case _:
            return None, None


def collect_hole_judgments(
    ctx: TypingContext,
    term: Term,
    expected: Type,
    refined_types: bool = True,
) -> dict[Name, tuple[Type, TypingContext]]:
    """Map each hole name to ``(expected_type, typing_context)`` at its occurrence."""
    match term:
        case Annotation(expr=Hole(name=n), type=hty):
            hty = _norm_ty(hty, refined_types)
            return {n: (hty, ctx)}
        case Hole(name=n):
            return {n: (_norm_ty(expected, refined_types), ctx)}
        case Annotation(expr=expr, type=ty):
            ty = _norm_ty(ty, refined_types)
            return collect_hole_judgments(ctx, expr, ty, refined_types)
        case Abstraction(var_name=v, body=body):
            match expected:
                case AbstractionType(vn, vt, rt):
                    body_expected = substitution_in_type(rt, Var(v), vn)
                    return collect_hole_judgments(ctx.with_var(v, vt), body, body_expected, refined_types)
                case _:
                    raise AssertionError(f"Abstraction typed with non-arrow type {expected}")
        case Application(fun=fun, arg=arg):
            if get_holes(fun):
                return collect_hole_judgments(ctx, fun, expected, refined_types) | collect_hole_judgments(
                    ctx, arg, expected, refined_types
                )
            _, ty_fun = synth(ctx, fun)
            match ty_fun:
                case AbstractionType(_, atype, _):
                    hs_fun = collect_hole_judgments(ctx, fun, ty_fun, refined_types)
                    hs_arg = collect_hole_judgments(ctx, arg, atype, refined_types)
                    return hs_fun | hs_arg
                case _:
                    return collect_hole_judgments(ctx, fun, expected, refined_types) | collect_hole_judgments(
                        ctx, arg, expected, refined_types
                    )
        case If(cond=cond, then=then, otherwise=otherwise):
            return (
                collect_hole_judgments(ctx, cond, t_bool, refined_types)
                | collect_hole_judgments(ctx, then, expected, refined_types)
                | collect_hole_judgments(ctx, otherwise, expected, refined_types)
            )
        case TypeApplication(body=body, type=_):
            _, ty_body = synth(ctx, body)
            match ty_body:
                case TypePolymorphism(_, _, _):
                    return collect_hole_judgments(ctx, body, ty_body, refined_types)
                case _:
                    return collect_hole_judgments(ctx, body, expected, refined_types)
        case Var(_) | Literal(_, _):
            return {}
        case _:
            raise AssertionError(f"tactics: unsupported term shape in collect_hole_judgments: {term}")


def list_hole_infos(
    ctx: TypingContext,
    term: Term,
    root_expected: Type,
    refined_types: bool = True,
) -> list[HoleInfo]:
    raw = collect_hole_judgments(ctx, term, root_expected, refined_types)
    out: list[HoleInfo] = []
    for name, (ety, hctx) in raw.items():
        rn, rp = hole_constraint_fields(ety)
        out.append(HoleInfo(name=name, ctx=hctx, expected=ety, refinement_name=rn, refinement_predicate=rp))
    return out


def replace_hole(term: Term, hole_name: Name, replacement: Term) -> Term:
    return substitution(term, replacement, hole_name)
