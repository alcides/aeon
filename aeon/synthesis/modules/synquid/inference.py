"""Infer E-terms when an argument's shape has not yet been discovered.

There is no catalogue of guessed instantiation types: component signatures and
chosen arguments supply shapes, and the persistent subtype queue relates fresh
unknowns until later construction steps determine them (Fig. 6).
"""

from dataclasses import dataclass
from time import monotonic

from aeon.core.instantiation import type_substitution
from aeon.core.substitutions import instantiate_refinement_with_horn_in_type, substitution
from aeon.core.terms import (
    Term,
    Var,
    Literal,
    Application,
    TypeApplication,
    RefinementApplication,
    ImplicitRefinementHole,
)
from aeon.core.types import Type, TypePolymorphism, RefinementPolymorphism, AbstractionType, t_int, t_bool, t_string
from aeon.synthesis.modules.synquid.constraints import ConstraintState, fresh_name
from aeon.synthesis.modules.synquid.round_trip import ApplicationState
from aeon.synthesis.modules.synquid.solver import Status
from aeon.typechecking.typeinfer import synth
from aeon.errors import AeonError


@dataclass
class InferredArgument:
    term: Term
    type: Type
    state: ConstraintState


def infer_terms(ctx, level, skip, mem, state):
    from aeon.synthesis.modules.synquid.engine import _arg_gen
    from aeon.verification.constructor_registry import get_constructor_groups

    for literal in (
        Literal(0, t_int),
        Literal(1, t_int),
        Literal(True, t_bool),
        Literal(False, t_bool),
        Literal("", t_string),
    ):
        vc, ty = synth(state.context, literal)
        child = state.fork()
        child.add(vc)
        yield InferredArgument(literal, ty, child)
    for name, typ in ctx.concrete_vars():
        if monotonic() >= state.deadline:
            return
        if skip(name) or name.name.endswith("_rec") and name.name[:-4] in get_constructor_groups():
            continue
        child = state.fork()
        head = Var(name)
        while isinstance(typ, (TypePolymorphism, RefinementPolymorphism)):
            if isinstance(typ, TypePolymorphism):
                instance = child.fresh_variable(typ.kind)
                head = TypeApplication(head, instance)
                typ = type_substitution(typ.body, typ.name, instance)
            else:
                predicate = child.refinement_parameter(typ.sort)
                head = RefinementApplication(head, ImplicitRefinementHole(fresh_name("implicit")))
                typ = instantiate_refinement_with_horn_in_type(typ.body, typ.name, typ.sort, predicate.name)
        if not isinstance(typ, AbstractionType):
            if isinstance(head, Var):
                vc, typ = synth(child.context, head)
                child.add(vc)
            yield InferredArgument(head, typ, child)
            continue
        # Higher-order arguments can be existing function components even when
        # their input/output instantiations have not yet been determined.
        yield InferredArgument(head, typ, child.fork())
        if level <= 0:
            continue
        result = typ
        while isinstance(result, AbstractionType):
            result = result.type
        app = ApplicationState.start(child, typ, result)

        def arguments(term, application, filling=False):
            if monotonic() >= state.deadline:
                return
            if application.state.solve() in (Status.INVALID, Status.EXHAUSTED):
                return
            if not application.params:
                if application.deferred:
                    deferred = ApplicationState(
                        application.state.fork(), application.deferred, application.result, application.goal
                    )
                    yield from arguments(term, deferred, True)
                    return
                yield InferredArgument(term, application.state.resolve(application.result), application.state)
                return
            binder, expected = application.params[0]
            expected = application.state.resolve(expected)
            if isinstance(expected, AbstractionType) and len(application.params) > 1 and not filling:
                deferred = ApplicationState(
                    application.state.fork(),
                    application.params[1:],
                    application.result,
                    application.goal,
                    application.deferred + [(binder, expected)],
                )
                yield from arguments(Application(term, Var(binder)), deferred)
                return
            for arg in _arg_gen(ctx, level, expected, skip, mem, application.state):
                try:
                    selected = application.choose(arg)
                except (ValueError, AssertionError, AeonError):
                    continue
                actual = arg.term if isinstance(arg, InferredArgument) else arg
                filled = substitution(term, actual, binder) if filling else Application(term, actual)
                yield from arguments(filled, selected, filling)

        yield from arguments(head, app)
