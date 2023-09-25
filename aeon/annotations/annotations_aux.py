from __future__ import annotations

from aeon.core.terms import Abstraction
from aeon.core.terms import Application
from aeon.core.terms import Let
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.core.types import AbstractionType
from aeon.core.types import BaseType
from aeon.utils.ast_helpers import ensure_anf_app
from aeon.utils.ast_helpers import ensure_anf_rec

forall_functions_types = {
    "forAllInts": AbstractionType(type=BaseType(name="Bool"), var_name="x", var_type=BaseType(name="Int")),
    "forAllFloats": AbstractionType(type=BaseType(name="Bool"), var_name="x", var_type=BaseType(name="Float")),
    "forAllLists": AbstractionType(type=BaseType(name="Bool"), var_name="x", var_type=BaseType(name="List")),
}


class FreshHelper:
    def __init__(self):
        self.counter = 0

    def fresh(self) -> str:
        self.counter += 1
        return f"_anf_fitness_{self.counter}"

    def __call__(self, *args, **kwargs):
        return self.fresh()


fresh = FreshHelper()


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

    return ensure_anf_rec(
        Rec(
            var_name=f"{term.var_name}",
            var_type=abs_type,
            var_value=term.var_value,
            body=fitness_return,
        ),
    )


def _transform_to_aeon_list(handled_terms: list[Term]):
    return_list_terms = [
        rec.body for rec in handled_terms if isinstance(rec, Rec) and isinstance(rec.body, Application)
    ]
    return_aeon_list = Var("List_new")
    for term in return_list_terms:
        return_aeon_list = ensure_anf_app(
            fresh,
            Application(ensure_anf_app(fresh, Application(Var("List_append_float"), return_aeon_list)), term),
        )

    nested_rec = return_aeon_list
    for current_rec in handled_terms[::-1]:
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
