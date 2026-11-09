"""Every synthesis validation route can check deep data without rewriting its scores."""

import pytest

from aeon.backend.evaluator import EvaluationContext, eval
from aeon.core.substitutions import substitution
from aeon.core.terms import Abstraction, Application, If, Let, Literal, Var
from aeon.core.types import t_bool, t_int
from aeon.synthesis.constructors import prepare_candidate
from aeon.synthesis.entrypoint import make_validator
from aeon.synthesis.expression_size import expression_size
from aeon.synthesis.joint import JointCandidate
from aeon.synthesis.modules.tdsyn.helpers import monomorphize
from aeon.synthesis.program_specifications import ProgramSpecifications
from aeon.utils.name import Name
from tests.tdsyn_arrays_test import _driver, _hole
from tests.tdsyn_relations_test import MASK


def mask_candidate(driver):
    hole = _hole(driver)
    constructors = {
        name.name: monomorphize(name, ty, hole.context, hole.expected_type)[0][0]
        for name, ty in hole.context.vars()
        if name.name in ("Mask_empty", "Mask_cons")
    }
    term = constructors["Mask_empty"]
    for _ in range(3):
        term = Application(Application(constructors["Mask_cons"], term), Literal(False, t_bool))
    return term


@pytest.mark.parametrize("whole_program", [False, True])
def test_shared_validators_name_data_but_keep_the_original_candidate(whole_program, monkeypatch):
    from aeon.synthesis import entrypoint, program_specifications

    driver = _driver(
        MASK
        + """
        def main (u:Int):{m:Mask{|fun w => fun rest => w + rest <= 0|} |
            Mask.count m = 3 && Mask.weight m = 0} := ?result;
    """
    )
    with driver.session.activate():
        term = mask_candidate(driver)
        before = expression_size(term)
        target = driver.incomplete_functions[0][1][0]
        module = program_specifications if whole_program else entrypoint
        original_check = module.check_type
        checked = []

        def check(ctx, program, ty):
            checked.append(program)
            return original_check(ctx, program, ty)

        monkeypatch.setattr(module, "check_type", check)
        if whole_program:
            with ProgramSpecifications(
                driver.typing_ctx,
                driver.evaluation_ctx,
                driver.core,
                driver.incomplete_functions,
                driver.metadata,
                pooled=False,
            ) as specs:
                candidate = specs.candidate({target: term})
                expected_program = specs.replace(candidate)
                assert specs.validate(candidate)
                assert specs.mapping(candidate)[target] is term
                assert specs.replace(candidate) == expected_program
        else:
            validate = make_validator(
                driver.typing_ctx, lambda value: substitution(driver.core, value, target), driver.metadata
            )
            assert validate(term)
        assert checked and "_data" in str(checked[0])
        assert expression_size(term) == before
        assert not isinstance(term, Let)
        shared = prepare_candidate(term)
        assert prepare_candidate(shared) is shared


def test_preparation_keeps_constructor_work_in_its_branch_and_lambda():
    driver = _driver("""
        inductive Chain | end:Chain | node (head:Int) (tail:Chain):Chain
        def main (u:Int):Chain := ?result;
    """)
    with driver.session.activate():
        names = {n.name: n for n, _ in _hole(driver).context.vars()}
        node, end, flag = names["Chain_node"], names["Chain_end"], Name("flag", 90001)
        inner = Application(Application(Var(node), Literal(2, t_int)), Var(end))
        tree = Application(Application(Var(node), Literal(1, t_int)), inner)
        original = Abstraction(flag, If(Var(flag), tree, Var(end)))
        prepared = prepare_candidate(original)
        assert isinstance(prepared, Abstraction) and isinstance(prepared.body, If)
        assert isinstance(prepared.body.then, Let)
        events = []

        def constructor(head):
            events.append(head)
            return lambda tail: (head, tail)

        ctx = EvaluationContext({node: constructor, end: ()})
        for choose in [False, True]:
            events.clear()
            expected = eval(original, ctx)(choose)
            expected_events = list(events)
            events.clear()
            assert eval(prepared, ctx)(choose) == expected
            assert events == expected_events == ([1, 2] if choose else [])
        joint = JointCandidate((original, tree))
        shared_joint = prepare_candidate(joint)
        assert isinstance(shared_joint, JointCandidate)
        assert isinstance(shared_joint.terms[1], Let)
        assert joint.terms[1] is tree
