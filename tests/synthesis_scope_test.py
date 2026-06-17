"""The fitness/example/cluster helpers emitted by the optimization decorators
must stay evaluable (in the program) but must not leak into the synthesis scope,
without relying on a ``__internal__`` name prefix."""

from __future__ import annotations

from aeon.synthesis.identification import get_holes_info
from aeon.synthesis.scope import close_synthesis_context, fitness_relevant_names
from aeon.core.types import top
from aeon.typechecking.context import TypingContext, TypeBinder, VariableBinder, UninterpretedBinder
from aeon.core.types import t_int
from aeon.utils.name import Name

from tests.driver import check_and_return_core


# --------------------------------------------------------------------------- #
# Unit: closing a context over recorded fitness names
# --------------------------------------------------------------------------- #


def _goal(name: Name):
    from aeon.synthesis.decorators import Goal

    return Goal(minimize=True, length=1, function=name, kind="expression")


def test_fitness_relevant_names_gathers_all_kinds():
    from aeon.synthesis.decorators import Example

    md = {
        Name("f", 0): {
            "goals": [_goal(Name("_fitness_minimize_f_0", 5))],
            "examples": [Example(Name("_example_f_0", 6), "f 1 == 1")],
            "cluster": Name("_cluster_f", 7),
        }
    }
    assert fitness_relevant_names(md) == {"_fitness_minimize_f_0", "_example_f_0", "_cluster_f"}


def test_close_context_drops_only_fitness_value_binders():
    md = {Name("f", 0): {"goals": [_goal(Name("_fitness_minimize_f_0", 5))]}}
    ctx = TypingContext(
        entries=[
            TypeBinder(Name("Int", 0)),
            VariableBinder(Name("f", 0), t_int),
            VariableBinder(Name("_fitness_minimize_f_0", 5), t_int),
            UninterpretedBinder(Name("g", 0), t_int),
        ]
    )
    closed = close_synthesis_context(ctx, md)
    names = {e.name.name for e in closed.entries if isinstance(e, (VariableBinder, UninterpretedBinder))}
    assert "_fitness_minimize_f_0" not in names
    assert {"f", "g"} <= names
    # type binders are untouched
    assert any(isinstance(e, TypeBinder) for e in closed.entries)
    # nothing to hide -> same object back
    assert close_synthesis_context(ctx, {}) is ctx


# --------------------------------------------------------------------------- #
# End-to-end: through the real decorator + lowering pipeline
# --------------------------------------------------------------------------- #

SOURCE = """
    @minimize(g(1.0) - 5.0)
    def g(x:Float) : Float := x

    def h(y:Float) : Float := ?hole
"""


def test_no_internal_prefix_in_generated_names():
    _core, _ctx, _ectx, metadata = check_and_return_core(SOURCE)
    names = fitness_relevant_names(metadata)
    assert names, "expected at least one fitness helper"
    assert all(not n.startswith("__internal__") for n in names)


def test_fitness_helpers_excluded_from_hole_scope_but_kept_in_program():
    core, ctx, _ectx, metadata = check_and_return_core(SOURCE)
    fitness = fitness_relevant_names(metadata)

    holes = get_holes_info(ctx, core, top, [], refined_types=True)
    # ``g``'s fitness helper is bound after ``g`` and so is in scope at the
    # later hole in ``h`` — exactly the leak the synthesizers used to filter.
    leaked = False
    for _ty, hole_ctx in holes.values():
        in_scope = {n.name for n, _t in hole_ctx.concrete_vars()}
        if fitness & in_scope:
            leaked = True
            closed = close_synthesis_context(hole_ctx, metadata)
            closed_scope = {n.name for n, _t in closed.concrete_vars()}
            # The closed synthesis scope must not contain the fitness helper...
            assert not (fitness & closed_scope), "fitness helper leaked into the closed synthesis scope"
            # ...while the real definitions stay available to the synthesizer.
            assert "g" in closed_scope
    assert leaked, "expected the fitness helper to be in scope at some hole"
