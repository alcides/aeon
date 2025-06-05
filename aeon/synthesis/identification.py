from aeon.core.substitutions import substitute_vartype, substitution_in_type
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    Hole,
    If,
    Let,
    Literal,
    Rec,
    Term,
    TypeAbstraction,
    TypeApplication,
    Var,
)
from aeon.core.types import AbstractionType, TypePolymorphism, TypeVar, refined_to_unrefined_type
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
    ty = ty if refined_types else refined_to_unrefined_type(ty)
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
            hs2 = get_holes_info(ctx, arg, ty, targets, refined_types)
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
        case Rec(var_name=vname, var_type=vtype, var_value=value, body=body):
            vtype = vtype if refined_types else refined_to_unrefined_type(vtype)
            if isinstance(vtype, AbstractionType) or isinstance(vtype, TypePolymorphism):
                hs1 = get_holes_info(ctx.with_var(vname, vtype), value, vtype, targets, refined_types)
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

        case _:
            assert False, f"Could not infer the type of {t} for synthesis."


def get_holes(term: Term) -> list[Name]:
    """Returns the names of holes in a particular term."""
    match term:
        case Hole(name=name):
            return [name]
        case Hole(name=name):
            return [name]
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
        case Rec(var_name=_, var_type=_, var_value=value, body=body):
            return get_holes(value) + get_holes(body)
        case TypeApplication(body=body, type=_):
            return get_holes(body)
        case TypeAbstraction(name=_, kind=_, body=body):
            return get_holes(body)
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
