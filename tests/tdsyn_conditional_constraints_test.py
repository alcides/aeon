"""Mutually exclusive arms must not impose simultaneous witness facts."""

import pytest

from aeon.compilation.session import CompilationSession
from aeon.core.parser import parse_type
from aeon.core.terms import Hole, Literal
from aeon.core.types import t_int
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.modules.tdsyn.actions import backward_if_candidates
from aeon.synthesis.modules.tdsyn.constraints import candidate_feasible, eager_pruning
from aeon.synthesis.modules.tdsyn.smt_solve import solve_literals
from aeon.synthesis.modules.tdsyn.worklist import PartialAST, TypedHole, expand_at_hole
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.ctx_helpers import built_std_context
from aeon.utils.name import Name


def compile_source(source, *, contracts=False):
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, contracts=contracts))
    errors = list(driver.parse(aeon_code=source))
    return driver, errors


@pytest.mark.parametrize("eager", [False, True])
def test_pruning_keeps_a_valid_conditional(eager):
    source = """
    def choose(x:{v:Int | v = 0 || v = 1}):{r:Int | r = x} :=
        if x = 0 then 0 else 1;
    def main(_ :Int):Int := choose 1;
    """
    driver, errors = compile_source(source)
    assert not errors
    assert driver.run() == 1
    with CompilationSession().activate():
        ctx = built_std_context().with_var(Name("x"), parse_type("{v:Int | v == 0 || v == 1}"))
        root = TypedHole(Name("result", 0), parse_type("{v:Int | v == x}"), ctx)
        partial = PartialAST(Hole(root.name), [root], 0)
        replacement, children = backward_if_candidates(root, lambda _: False)[0]
        partial = expand_at_hole(partial, root, replacement, children, 1)
        then = next(h for h in partial.holes if h.name == children[1].name)
        partial = expand_at_hole(partial, then, Literal(0, t_int), [], 2)
        otherwise = next(h for h in partial.holes if h.name == children[2].name)
        token = eager_pruning.set(eager)
        try:
            assert candidate_feasible(otherwise, Literal(1, t_int), [])
        finally:
            eager_pruning.reset(token)


def test_literal_completion_can_select_the_only_feasible_branch():
    with CompilationSession().activate():
        ctx = built_std_context().with_var(Name("x"), parse_type("{v:Int | v == 1}"))
        root = TypedHole(Name("result", 0), parse_type("{v:Int | v == x}"), ctx)
        partial = PartialAST(Hole(root.name), [root], 0)
        replacement, children = backward_if_candidates(root, lambda _: False)[0]
        partial = expand_at_hole(partial, root, replacement, children, 1)
        for original, value in zip(children[1:], [0, 1]):
            branch = next(h for h in partial.holes if h.name == original.name)
            partial = expand_at_hole(partial, branch, Literal(value, t_int), [], 2)
        assert len(partial.holes) == 1
        condition = partial.holes[0]
        solutions = solve_literals(partial.holes)
        assert solutions
        assert all(solution[condition.name].value is False for solution in solutions)


def test_two_impossible_branches_are_still_rejected():
    with CompilationSession().activate():
        root = TypedHole(Name("result", 0), parse_type("{v:Int | v > 0}"), built_std_context())
        partial = PartialAST(Hole(root.name), [root], 0)
        replacement, children = backward_if_candidates(root, lambda _: False)[0]
        partial = expand_at_hole(partial, root, replacement, children, 1)
        then = next(h for h in partial.holes if h.name == children[1].name)
        partial = expand_at_hole(partial, then, Literal(-1, t_int), [], 2)
        otherwise = next(h for h in partial.holes if h.name == children[2].name)
        assert not candidate_feasible(otherwise, Literal(-2, t_int), [])
