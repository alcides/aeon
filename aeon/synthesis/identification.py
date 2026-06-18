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

    Args:
        ctx (TypingContext): The current TypingContext.
        t (Term): The term to analyze.
        ty (Type): The current type.
        targets (list(tuple(str, list(str)))): List of tuples functions names that contains holes and the name holes
        refined_types (bool): Whether to use refined types.
    """
    # ty = ty if refined_types else refined_to_unrefined_type(ty)
    # Hole identification only needs to descend into subterms that actually
    # contain a hole. Skipping hole-free subterms avoids re-typing
    # already-elaborated library code: a polymorphic definition such as
    # ``List.map`` (whose body mentions ``cons``/``map`` carrying abstract
    # refinements) produces term/type shapes the arms below do not model, and
    # previously aborted the whole traversal with ``assert False``. Such
    # subterms contribute no holes, so returning early is both correct and
    # strictly faster.
    if not get_holes(t):
        return {}
    match t:
        case Annotation(expr=Hole(name=hname), type=hty):
            hty = hty if refined_types else refined_to_unrefined_type(hty)
            return {hname: (hty, ctx)} if hname != "main" else {}
        case Hole(name=hname):
            return {hname: (ty, ctx)} if hname != "main" else {}
        case Literal(_, _):
            return {}
        case Var(_):
            return {}
        case Annotation(expr=expr, type=ty):
            ty = ty if refined_types else refined_to_unrefined_type(ty)
            return get_holes_info(ctx, expr, ty, targets, refined_types)
        case Application(fun=fun, arg=arg):
            hs1 = get_holes_info(ctx, fun, ty, targets, refined_types)
            # Determine the argument type from the function's type when possible.
            try:
                _, fun_ty = synth(ctx, fun)
                arg_ty = fun_ty.var_type if isinstance(fun_ty, AbstractionType) else ty
            except Exception:
                arg_ty = ty
            hs2 = get_holes_info(ctx, arg, arg_ty, targets, refined_types)
            return hs1 | hs2
        case If(cond=cond, then=then, otherwise=otherwise):
            hs1 = get_holes_info(ctx, cond, ty, targets, refined_types)
            hs2 = get_holes_info(ctx, then, ty, targets, refined_types)
            hs3 = get_holes_info(ctx, otherwise, ty, targets, refined_types)
            return hs1 | hs2 | hs3
        case Abstraction(var_name=vname, body=body):
            if isinstance(ty, AbstractionType):
                ret = substitution_in_type(ty.type, Var(vname), ty.var_name)
                ctx = ctx.with_var(vname, ty.var_type)
                return get_holes_info(ctx, body, ret, targets, refined_types)
            else:
                assert False, f"Synthesis cannot infer the type of {t} with type {ty}"
        case Let(var_name=vname, var_value=value, body=body):
            _, t1 = synth(ctx, value)
            t1 = t1 if refined_types else refined_to_unrefined_type(t1)
            if not isinstance(value, Hole) and not (isinstance(value, Annotation) and isinstance(value.expr, Hole)):
                ctx = ctx.with_var(vname, t1)
                hs1 = get_holes_info(ctx, t.var_value, ty, targets, refined_types)
                hs2 = get_holes_info(ctx, t.body, ty, targets, refined_types)
            else:
                hs1 = get_holes_info(ctx, t.var_value, ty, targets, refined_types)
                ctx = ctx.with_var(vname, t1)
                hs2 = get_holes_info(ctx, t.body, ty, targets, refined_types)
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
                hs1 = get_holes_info(value_ctx, value, vtype, targets, refined_types)
            else:
                hs1 = get_holes_info(ctx, value, vtype, targets, refined_types)
            hs2 = get_holes_info(ctx.with_var(vname, vtype), body, ty, targets, refined_types)
            return hs1 | hs2
        case TypeApplication(body=body, type=argty):
            _, bty = synth(ctx, body)
            argty = argty if refined_types else refined_to_unrefined_type(argty)
            if isinstance(bty, TypePolymorphism):
                ntype = substitute_vartype(bty.body, argty, bty.name)
                ntype = ntype if refined_types else refined_to_unrefined_type(ntype)
                return get_holes_info(ctx, body, ntype, targets, refined_types)
            else:
                assert False, f"Synthesis cannot infer the type of {t}"
        case TypeAbstraction(name=n, kind=k, body=body):
            match ty:
                case TypePolymorphism(n2, k2, ity):
                    assert k == k2, "Kinds do not match"
                    return get_holes_info(
                        ctx.with_typevar(n, k), body, substitute_vartype(ity, TypeVar(n), n2), targets, refined_types
                    )
                case _:
                    assert False, "TypeAbstraction does not have the TypePolymorphism type."
        case RefinementAbstraction(name=_, sort=_, body=body):
            # The refinement parameter is solved by Horn inference, not GP
            # synthesis. Walk under the binder with the inner type.
            inner_ty = ty.body if isinstance(ty, RefinementPolymorphism) else ty
            return get_holes_info(ctx, body, inner_ty, targets, refined_types)
        case RefinementApplication(body=body, refinement=_):
            # Implicit refinement application — synthesis ignores the
            # refinement (Horn solves it) and recurses into the function.
            return get_holes_info(ctx, body, ty, targets, refined_types)

        case _:
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
    return [(rec.var_name, get_holes(rec.var_value)) for rec in iterate_top_level(term) if get_holes(rec.var_value)]
