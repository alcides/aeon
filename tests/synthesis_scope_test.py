"""The fitness/example/cluster helpers emitted by the optimization decorators
must stay evaluable (in the program) but must be hidden from the synthesis scope
by let-shadowing to ``Unit`` — not by a ``__internal__`` name prefix."""

from __future__ import annotations

from aeon.synthesis.identification import get_holes_info
from aeon.synthesis.scope import fitness_relevant_names, shadow_fitness_helpers
from aeon.core.types import top, t_int, t_unit
from aeon.typechecking.context import TypingContext, TypeBinder, VariableBinder, UninterpretedBinder
from aeon.utils.name import Name

from tests.driver import check_and_return_core


# --------------------------------------------------------------------------- #
# Unit: shadowing recorded fitness helpers to Unit
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


def test_shadow_rebinds_only_in_scope_helpers_to_unit():
    md = {Name("f", 0): {"goals": [_goal(Name("_fitness_minimize_f_0", 5))]}}
    ctx = TypingContext(
        entries=[
            TypeBinder(Name("Int", 0)),
            VariableBinder(Name("f", 0), t_int),
            VariableBinder(Name("_fitness_minimize_f_0", 5), t_int),  # real (callable) type
            UninterpretedBinder(Name("g", 0), t_int),
        ]
    )
    shadowed = shadow_fitness_helpers(ctx, md)
    vars_by_name = {n.name: t for n, t in shadowed.concrete_vars()}
    # the helper is now seen as inert Unit, not its real type
    assert vars_by_name["_fitness_minimize_f_0"] == t_unit
    # real definitions are untouched
    assert vars_by_name["f"] == t_int
    # nothing to shadow -> same object back
    assert shadow_fitness_helpers(ctx, {}) is ctx
    # a recorded helper that is not in scope is not introduced
    md2 = {Name("z", 0): {"goals": [_goal(Name("_fitness_minimize_z_0", 9))]}}
    assert shadow_fitness_helpers(ctx, md2) is ctx


# --------------------------------------------------------------------------- #
# End-to-end through the real decorator + lowering pipeline
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


def test_fitness_helper_shadowed_to_unit_at_later_hole():
    core, ctx, _ectx, metadata = check_and_return_core(SOURCE)
    fitness = fitness_relevant_names(metadata)

    holes = get_holes_info(ctx, core, top, [], refined_types=True)
    shadowed_somewhere = False
    for _ty, hole_ctx in holes.values():
        in_scope = {n.name for n, _t in hole_ctx.concrete_vars()}
        if fitness & in_scope:  # g's fitness helper is in scope at h's hole
            shadowed_somewhere = True
            shadowed = shadow_fitness_helpers(hole_ctx, metadata)
            types_by_name = {n.name: t for n, t in shadowed.concrete_vars()}
            for fn in fitness & in_scope:
                # hidden by shadowing to the inert Unit type, not removed
                assert types_by_name[fn] == t_unit
            assert "g" in types_by_name  # the real definition stays available
    assert shadowed_somewhere, "expected a fitness helper in scope at some hole"
