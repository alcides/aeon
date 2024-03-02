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
from aeon.core.types import AbstractionType, TypePolymorphism
from aeon.core.types import Type
from aeon.core.types import refined_to_unrefined_type
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import synth


# dict (hole_name , (hole_type, hole_typingContext))
def get_holes_info(
    ctx: TypingContext,
    t: Term,
    ty: Type,
    targets: list[tuple[str, list[str]]],
) -> dict[str, tuple[Type, TypingContext]]:
    """Retrieve the Types of "holes" in a given Term and TypingContext.

    This function recursively navigates through the Term 't', updating the TypingContext and hole Type as necessary.
    When a hole is found, its Type and the current TypingContext are added to a dictionary, with the hole name as key.

    Args:
        ctx (TypingContext): The current TypingContext.
        t (Term): The term to analyze.
        ty (Type): The current type.
        targets (list(tuple(str, list(str)))): List of tuples functions names that contains holes and the name holes
    """
    match t:
        case Annotation(expr=Hole(name=hname), type=ty):
            ty = refined_to_unrefined_type(ty)
            return {hname: (ty, ctx)} if hname != "main" else {}
        case Hole(name=hname):
            ty = refined_to_unrefined_type(ty)
            return {hname: (ty, ctx)} if hname != "main" else {}
        case Literal(_, _):
            return {}
        case Var(_):
            return {}
        case Annotation(expr=expr, type=ty):
            return get_holes_info(ctx, expr, ty, targets)
        case Application(fun=fun, arg=arg):
            hs1 = get_holes_info(ctx, fun, ty, targets)
            hs2 = get_holes_info(ctx, arg, ty, targets)
            return hs1 | hs2
        case If(cond=cond, then=then, otherwise=otherwise):
            hs1 = get_holes_info(ctx, cond, ty, targets)
            hs2 = get_holes_info(ctx, then, ty, targets)
            hs3 = get_holes_info(ctx, otherwise, ty, targets)
            return hs1 | hs2 | hs3
        case Abstraction(var_name=vname, body=body):
            if isinstance(ty, AbstractionType):
                ret = substitution_in_type(ty.type, Var(vname), ty.var_name)
                ctx = ctx.with_var(vname, ty.var_type)
                return get_holes_info(ctx, body, ret, targets)
            else:
                assert False, f"Synthesis cannot infer the type of {t}"
        case Let(var_name=vname, var_value=value, body=body):
            _, t1 = synth(ctx, value)
            if not isinstance(value, Hole) and not (isinstance(value, Annotation) and isinstance(value.expr, Hole)):
                ctx = ctx.with_var(vname, t1)
                hs1 = get_holes_info(ctx, t.var_value, ty, targets)
                hs2 = get_holes_info(ctx, t.body, ty, targets)
            else:
                hs1 = get_holes_info(ctx, t.var_value, ty, targets)
                ctx = ctx.with_var(vname, t1)
                hs2 = get_holes_info(ctx, t.body, ty, targets)
            return hs1 | hs2
        case Rec(var_name=vname, var_type=vtype, var_value=value, body=body):
            if any(tup[0] == vname for tup in targets):
                hs1 = get_holes_info(ctx, value, vtype, targets)
                ctx = ctx.with_var(vname, vtype)
                hs2 = get_holes_info(ctx, body, ty, targets)
            else:
                ctx = ctx.with_var(vname, vtype)
                hs1 = get_holes_info(ctx, value, vtype, targets)
                hs2 = get_holes_info(ctx, body, ty, targets)

            return hs1 | hs2
        case TypeApplication(body=body, type=argty):
            if isinstance(ty, TypePolymorphism):
                ntype = substitute_vartype(ty.body, argty, ty.name)
                return get_holes_info(ctx, body, ntype, targets)
            else:
                assert False, f"Synthesis cannot infer the type of {t}"
        case TypeAbstraction(name=n, kind=k, body=body):
            return get_holes_info(ctx.with_typevar(n, k), body, ty, targets)
        case _:
            assert False, f"Could not infer the type of {t} for synthesis."


def get_holes(term: Term) -> list[str]:
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


def incomplete_functions_and_holes(ctx: TypingContext, term: Term) -> list[tuple[str, list[str]]]:
    """Given a typing context and a term, this function identifies which top-
    level functions have holes, and returns a list of holes in each
    function."""
    return [(rec.var_name, get_holes(rec.var_value)) for rec in iterate_top_level(term) if get_holes(rec.var_value)]
