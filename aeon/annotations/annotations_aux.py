from __future__ import annotations

from aeon.core.terms import Abstraction
from aeon.core.terms import Application
from aeon.core.terms import Let
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.core.types import AbstractionType
from aeon.core.types import BaseType


forall_functions_types = {
    "forAllInts": AbstractionType(type=BaseType(name="Bool"), var_name="x", var_type=BaseType(name="Int")),
    "forAllFloats": AbstractionType(type=BaseType(name="Bool"), var_name="x", var_type=BaseType(name="Float")),
    "forAllLists": AbstractionType(type=BaseType(name="Bool"), var_name="x", var_type=BaseType(name="List")),
}


def handle_term(term: Term, minimize_flag: bool | list[bool]) -> tuple[Term, bool | list[bool]]:
    if isinstance(term, Let):
        return _handle_let(term, minimize_flag)
    elif isinstance(term, Var):
        # TODO: handle Var type
        pass

    raise Exception(f"Term not handled by annotation: {type(term)}")


def _handle_let(term: Let, minimize_flag: bool | list[bool]) -> tuple[Term, bool | list[bool]]:
    if isinstance(term.body, Application):
        if isinstance(term.var_value, Abstraction):
            return _transform_to_fitness_term(term), minimize_flag
        else:
            return term, minimize_flag

    return term, minimize_flag


def _transform_to_fitness_term(term: Let) -> Term:
    abs_type = get_abstraction_type(term.body.fun)

    fitness_return = Application(arg=Var(f"{term.var_name}"), fun=Var(f"{term.body.fun.name}"))

    return Rec(
        var_name=f"{term.var_name}",
        var_type=abs_type,
        var_value=term.var_value,
        body=fitness_return,
    )


def _transform_to_aeon_list(handled_terms: list[Term]):
    return_list_terms = [
        rec.body for rec in handled_terms if isinstance(rec, Rec) and isinstance(rec.body, Application)
    ]

    # TODO: fix bug : ((List_append_float ((List_append_float (List_append_float List_new)) (forAllInts _anf_3))) (forAllInts _anf_6))));
    return_list = Application(Var("List_append_float"), Var("List_new"))
    for term in return_list_terms:
        return_list = Application(Application(Var("List_append_float"), return_list), term)

    nested_rec = return_list
    for current_rec in reversed(handled_terms):
        nested_rec = Rec(current_rec.var_name, current_rec.var_type, current_rec.var_value, nested_rec)

    return nested_rec


def handle_mutiple_terms(terms: list[Term], minimize_flags: bool | list[bool]) -> tuple[Term, bool | list[bool]]:
    handled_terms = [handle_term(term, flag)[0] for term, flag in zip(terms, minimize_flags)]

    fitness_body = _transform_to_aeon_list(handled_terms)
    return fitness_body, minimize_flags


def get_abstraction_type(term: Term) -> AbstractionType:
    if isinstance(term, Var):
        if term.name in forall_functions_types:
            return forall_functions_types[term.name]
    raise Exception(f"Not handled: {term}")
