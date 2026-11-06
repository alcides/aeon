"""Shared conversions and substitution for datatype predicate arguments."""

from aeon.core.liquid import LiquidApp, LiquidPredicate, LiquidVar
from aeon.core.terms import Abstraction, Term, ImplicitRefinementHole
from aeon.utils.name import Name, fresh_counter


def predicate_from_term(term: Term) -> LiquidPredicate:
    from aeon.core.substitutions import inline_lets, liquefy

    if isinstance(term, ImplicitRefinementHole):
        return LiquidPredicate((), LiquidVar(term.name), implicit=True)
    parameters = []
    while isinstance(term, Abstraction):
        parameters.append(term.var_name)
        term = term.body
    body = liquefy(inline_lets(term))
    if body is None:
        raise ValueError("Datatype arguments must be logical predicates")
    return LiquidPredicate(tuple(parameters), body)


def predicate_to_term(predicate: LiquidPredicate) -> Term:
    from aeon.core.terms import Var, Application, Literal, If
    from aeon.core.types import t_bool, t_int, t_float, t_string, t_unit
    from aeon.core.liquid import (
        LiquidLiteralBool,
        LiquidLiteralInt,
        LiquidLiteralFloat,
        LiquidLiteralString,
        LiquidLiteralUnit,
    )

    if predicate.implicit and isinstance(predicate.body, LiquidVar):
        return ImplicitRefinementHole(predicate.body.name)

    def convert(body):
        if isinstance(body, LiquidVar):
            return Var(body.name)
        if isinstance(body, LiquidLiteralUnit):
            return Literal(None, t_unit)
        for cls, ty in (
            (LiquidLiteralBool, t_bool),
            (LiquidLiteralInt, t_int),
            (LiquidLiteralFloat, t_float),
            (LiquidLiteralString, t_string),
        ):
            if isinstance(body, cls):
                return Literal(body.value, ty)
        if isinstance(body, LiquidApp):
            if body.fun.name == "ite" and len(body.args) == 3:
                return If(*(convert(arg) for arg in body.args))
            term = Var(body.fun)
            for argument in body.args:
                term = Application(term, convert(argument))
            return term
        raise ValueError("Unresolved datatype predicate")

    result = convert(predicate.body)
    for parameter in reversed(predicate.parameters):
        result = Abstraction(parameter, result)
    return result


def instantiate_predicate(predicate, name, replacement):
    from aeon.core.substitutions import instantiate_refinement_in_liquid

    if name in predicate.parameters:
        return predicate
    if not predicate.parameters and predicate.body == LiquidVar(name):
        return replacement if isinstance(replacement, LiquidPredicate) else predicate_from_term(replacement)
    return LiquidPredicate(predicate.parameters, instantiate_refinement_in_liquid(predicate.body, name, replacement))


def instantiate_predicate_horn(predicate, name, sort, horn_name):
    from aeon.core.substitutions import predicate_domains, instantiate_refinement_with_horn_in_liquid

    if name in predicate.parameters:
        return predicate
    if not predicate.parameters and predicate.body == LiquidVar(name):
        parameters = tuple(Name("predicate_arg", fresh_counter.fresh()) for _ in predicate_domains(sort))
        predicate = LiquidPredicate(parameters, LiquidApp(name, [LiquidVar(n) for n in parameters]))
    return LiquidPredicate(
        predicate.parameters, instantiate_refinement_with_horn_in_liquid(predicate.body, name, sort, horn_name)
    )


def map_predicate_types(predicate, transform):
    """Substitute the sorts carried by an inferred predicate's Horn slots."""
    from aeon.core.types import LiquidHornApplication, RefinedType

    def sort(ty):
        ty = transform(ty)
        return ty.type if isinstance(ty, RefinedType) else ty

    def visit(body):
        if isinstance(body, LiquidHornApplication):
            return LiquidHornApplication(body.name, [(visit(a), sort(t)) for a, t in body.argtypes], loc=body.loc)
        if isinstance(body, LiquidApp):
            return LiquidApp(body.fun, [visit(a) for a in body.args], loc=body.loc)
        return body

    return LiquidPredicate(predicate.parameters, visit(predicate.body), predicate.implicit)
