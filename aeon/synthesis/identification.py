from aeon.core.substitutions import substitute_vartype, substitution_in_type
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    Hole,
    If,
    ImplicitRefinementHole,
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
    RefinementPolymorphism,
    TypePolymorphism,
    TypeVar,
    refined_to_unrefined_type,
)
from aeon.core.types import Type
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import synth
from aeon.utils.name import Name


def term_has_holes(term: Term) -> bool:
    """Return whether ``term`` contains any synthesis ``Hole`` (not refinement holes).

    Short-circuits on the first hit so hole-free library subtrees are rejected
    in a single walk instead of building a name list.
    """
    match term:
        case Hole(_):
            return True
        case ImplicitRefinementHole(_):
            return False
        case Literal(_) | Var(_):
            return False
        case Annotation(expr=expr, type=_):
            return term_has_holes(expr)
        case Application(fun=fun, arg=arg):
            return term_has_holes(fun) or term_has_holes(arg)
        case If(cond=cond, then=then, otherwise=otherwise):
            return term_has_holes(cond) or term_has_holes(then) or term_has_holes(otherwise)
        case Abstraction(var_name=_, body=body):
            return term_has_holes(body)
        case Let(var_name=_, var_value=value, body=body):
            return term_has_holes(value) or term_has_holes(body)
        case Rec(var_name=_, var_type=_, var_value=value, body=body, decreasing_by=decr):
            return term_has_holes(value) or term_has_holes(body) or any(term_has_holes(m) for m in decr)
        case TypeApplication(body=body, type=_):
            return term_has_holes(body)
        case TypeAbstraction(name=_, kind=_, body=body):
            return term_has_holes(body)
        case RefinementAbstraction(name=_, body=body):
            return term_has_holes(body)
        case RefinementApplication(body=body, refinement=refinement):
            return term_has_holes(body) or term_has_holes(refinement)
        case _:
            return False


def _child_holes(
    ctx: TypingContext,
    child: Term,
    ty: Type,
    targets: list[tuple[Name, list[Name]]],
    refined_types: bool,
) -> dict[Name, tuple[Type, TypingContext]]:
    """Recurse into ``child`` only when it contains a synthesis hole."""
    if not term_has_holes(child):
        return {}
    return get_holes_info(ctx, child, ty, targets, refined_types)


# dict (hole_name , (hole_type, hole_typingContext))
def get_holes_info(
    ctx: TypingContext,
    t: Term,
    ty: Type,
    targets: list[tuple[Name, list[Name]]],
    refined_types: bool = False,
) -> dict[Name, tuple[Type, TypingContext]]:
    """Retrieve the Types of "holes" in a given Term and TypingContext.

    This function recursively navigates through the Term 't', updating the TypingContext and hole Type as necessary.
    When a hole is found, its Type and the current TypingContext are added to a dictionary, with the hole name as key.

    Hole-free children are skipped via :func:`term_has_holes` so already-elaborated
    library code is not re-typed (and cannot trip the fallthrough assert).
    """
    match t:
        case Annotation(expr=Hole(name=hname), type=hty):
            hty = hty if refined_types else refined_to_unrefined_type(hty)
            return {hname: (hty, ctx)} if hname != "main" else {}
        case Hole(name=hname):
            return {hname: (ty, ctx)} if hname != "main" else {}
        case Literal(_, _) | Var(_):
            return {}
        case Annotation(expr=expr, type=ann_ty):
            ann_ty = ann_ty if refined_types else refined_to_unrefined_type(ann_ty)
            return _child_holes(ctx, expr, ann_ty, targets, refined_types)
        case Application(fun=fun, arg=arg):
            hs1 = _child_holes(ctx, fun, ty, targets, refined_types)
            try:
                _, fun_ty = synth(ctx, fun)
                arg_ty = fun_ty.var_type if isinstance(fun_ty, AbstractionType) else ty
            except Exception:
                arg_ty = ty
            hs2 = _child_holes(ctx, arg, arg_ty, targets, refined_types)
            return hs1 | hs2
        case If(cond=cond, then=then, otherwise=otherwise):
            return (
                _child_holes(ctx, cond, ty, targets, refined_types)
                | _child_holes(ctx, then, ty, targets, refined_types)
                | _child_holes(ctx, otherwise, ty, targets, refined_types)
            )
        case Abstraction(var_name=vname, body=body):
            if isinstance(ty, AbstractionType):
                ret = substitution_in_type(ty.type, Var(vname), ty.var_name)
                return _child_holes(ctx.with_var(vname, ty.var_type), body, ret, targets, refined_types)
            else:
                assert False, f"Synthesis cannot infer the type of {t} with type {ty}"
        case Let(var_name=vname, var_value=value, body=body):
            _, t1 = synth(ctx, value)
            t1 = t1 if refined_types else refined_to_unrefined_type(t1)
            if not isinstance(value, Hole) and not (isinstance(value, Annotation) and isinstance(value.expr, Hole)):
                ctx = ctx.with_var(vname, t1)
                hs1 = _child_holes(ctx, value, ty, targets, refined_types)
                hs2 = _child_holes(ctx, body, ty, targets, refined_types)
            else:
                hs1 = _child_holes(ctx, value, ty, targets, refined_types)
                ctx = ctx.with_var(vname, t1)
                hs2 = _child_holes(ctx, body, ty, targets, refined_types)
            return hs1 | hs2
        case Rec(var_name=vname, var_type=vtype, var_value=value, body=body, decreasing_by=_):
            vtype = vtype if refined_types else refined_to_unrefined_type(vtype)
            # A ``mutual`` member's value may call its siblings; bring their
            # signatures into scope so a hole there is synthesised against a
            # context that knows the (co-synthesised) callees — the declared
            # refined type over-approximates each sibling's behaviour.
            value_ctx = ctx.with_var(vname, vtype)
            for comp in t.companions:
                ctype = comp.type if refined_types else refined_to_unrefined_type(comp.type)
                value_ctx = value_ctx.with_var(comp.name, ctype)
            if isinstance(vtype, AbstractionType) or isinstance(vtype, TypePolymorphism):
                hs1 = _child_holes(value_ctx, value, vtype, targets, refined_types)
            else:
                hs1 = _child_holes(ctx, value, vtype, targets, refined_types)
            hs2 = _child_holes(ctx.with_var(vname, vtype), body, ty, targets, refined_types)
            return hs1 | hs2
        case TypeApplication(body=body, type=argty):
            _, bty = synth(ctx, body)
            argty = argty if refined_types else refined_to_unrefined_type(argty)
            if isinstance(bty, TypePolymorphism):
                ntype = substitute_vartype(bty.body, argty, bty.name)
                ntype = ntype if refined_types else refined_to_unrefined_type(ntype)
                return _child_holes(ctx, body, ntype, targets, refined_types)
            else:
                assert False, f"Synthesis cannot infer the type of {t}"
        case TypeAbstraction(name=n, kind=k, body=body):
            match ty:
                case TypePolymorphism(n2, k2, ity):
                    assert k == k2, "Kinds do not match"
                    return _child_holes(
                        ctx.with_typevar(n, k),
                        body,
                        substitute_vartype(ity, TypeVar(n), n2),
                        targets,
                        refined_types,
                    )
                case _:
                    assert False, "TypeAbstraction does not have the TypePolymorphism type."
        case RefinementAbstraction(name=_, sort=_, body=body):
            # The refinement parameter is solved by Horn inference, not GP
            # synthesis. Walk under the binder with the inner type.
            inner_ty = ty.body if isinstance(ty, RefinementPolymorphism) else ty
            return _child_holes(ctx, body, inner_ty, targets, refined_types)
        case RefinementApplication(body=body, refinement=_):
            # Implicit refinement application — synthesis ignores the
            # refinement (Horn solves it) and recurses into the function.
            return _child_holes(ctx, body, ty, targets, refined_types)

        case _:
            # Unknown term shapes (e.g. some elaborated library forms) are safe
            # to skip when they contain no synthesis holes.
            if not term_has_holes(t):
                return {}
            assert False, f"Could not infer the type of {t} for synthesis."


def get_holes(term: Term) -> list[Name]:
    """Returns the names of holes in a particular term.

    ``ImplicitRefinementHole`` (inserted by elaboration when instantiating an
    ``RefinementPolymorphism``) is *not* a synthesis hole: it is solved by
    Horn inference, so this function returns ``[]`` for it. Since it is a
    distinct ``Term`` subclass — not a subclass of ``Hole`` — the
    ``case Hole(...)`` arm cannot match it, and the recursion through
    ``RefinementApplication`` lands on the dedicated leaf case below.
    """
    match term:
        case Hole(name=name):
            return [name]
        case ImplicitRefinementHole(_):
            return []
        case Literal(_):
            return []
        case Var(_):
            return []
        case Annotation(expr=expr, type=_):
            return get_holes(expr)
        case Application(fun=fun, arg=arg):
            return get_holes(fun) + get_holes(arg)
        case If(cond=cond, then=then, otherwise=otherwise):
            return get_holes(cond) + get_holes(then) + get_holes(otherwise)
        case Abstraction(var_name=_, body=body):
            return get_holes(body)
        case Let(var_name=_, var_value=value, body=body):
            return get_holes(value) + get_holes(body)
        case Rec(var_name=_, var_type=_, var_value=value, body=body, decreasing_by=decr):
            nested = [h for m in decr for h in get_holes(m)]
            return get_holes(value) + get_holes(body) + nested
        case TypeApplication(body=body, type=_):
            return get_holes(body)
        case TypeAbstraction(name=_, kind=_, body=body):
            return get_holes(body)
        case RefinementAbstraction(name=_, body=body):
            return get_holes(body)
        case RefinementApplication(body=body, refinement=refinement):
            return get_holes(body) + get_holes(refinement)
        case _:
            assert False


def iterate_top_level(term: Term):
    """Iterates through a program, and returns the top-level functions."""
    while isinstance(term, Rec):
        yield term
        term = term.body


def incomplete_functions_and_holes(ctx: TypingContext, term: Term) -> list[tuple[Name, list[Name]]]:
    """Given a typing context and a term, this function identifies which top-
    level functions have holes, and returns a list of holes in each
    function."""
    result: list[tuple[Name, list[Name]]] = []
    for rec in iterate_top_level(term):
        holes = get_holes(rec.var_value)
        if holes:
            result.append((rec.var_name, holes))
    return result
