"""Exercise combined intent through each general-purpose backend's real search.

Specialized input languages (controllers, DP transformations and Boolean CNF)
are covered in specialized_specifications_test; constructor learners and fixed
steps have their own suites. This checks interoperability, not search quality.
"""

import pytest

from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from tests.synthesis_specifications_test import solve


@pytest.mark.parametrize(
    "backend",
    [
        "tdsyn",
        "tdsyn_random",
        "synquid",
        "tactics",
        "enumerative",
        "random_search",
        "gp",
        "rl_mcts",
        "decision_tree",
        "contata",
        "bustle",
        "bustle_baseline",
        "fta",
        "afta",
        "cata",
        "lta",
        "arborist",
        "smt",
        "sygus",
        "polynomial",
        "amaze",
    ],
)
def test_combined_specs_reach_real_candidate_search(backend):
    implementation = make_synthesizer(backend)
    result = solve(
        r"""
        @doc("Return zero.")
        @example(f 0 = 0)
        @csv_data("0,0\n1,0")
        @minimize_int(f 0)
        @maximize_int(f 1)
        @minimize_size
        @minimize_cputime(f 0)
        @minimize_energy(f 0)
        def f(x:Int):{v:Int | v = 0} := ?body;
        @property(3) def law(x:Int):Bool := f x = 0;
        """,
        implementation,
        budget=3,
    )
    assert result and all(candidate is not None for candidate in result.values())
    assert implementation.pareto_front
    for scores, _ in implementation.pareto_front:
        # Example, CSV, min, max, size, CPU time, energy and property all reach
        # scoring together. The refinement uniquely determines the outputs.
        assert len(scores) == 8
        assert scores[:4] == [0.0] * 4
        assert scores[4] >= 1
        assert scores[5] >= 0 and scores[6] >= 0
        assert scores[7] == 0


@pytest.mark.parametrize("backend", ["symetric", "xfta"])
def test_metric_backends_combine_specs_in_a_numeric_output_space(backend):
    from aeon.core.terms import Literal
    from aeon.core.types import t_int

    result = solve(
        r"""
        @doc("Return zero.")
        @example(f = 0)
        @csv_data("0\n0")
        @minimize_int(f)
        @maximize_int(f)
        @minimize_size
        @minimize_cputime(f)
        @minimize_energy(f)
        def f:{v:Int | v = 0} := ?body;
        @property(2) def law(x:Bool):Bool := f = 0;
        """,
        make_synthesizer(backend),
        budget=3,
    )
    # SyMetric scalarizes goals; it does not advertise a Pareto archive.
    assert list(result.values()) == [Literal(0, t_int)]
