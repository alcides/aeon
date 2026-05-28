from aeon.core.terms import Hole, ImplicitRefinementHole, RefinementApplication, Var
from aeon.synthesis.identification import get_holes, incomplete_functions_and_holes
from aeon.utils.name import Name
from tests.driver import check_and_return_core


def extract_target_functions(source):
    core_ast_anf, ctx, _, _ = check_and_return_core(source)
    return incomplete_functions_and_holes(ctx, core_ast_anf)


def test_hole_identification():
    code = """
            def year : Int = 2023;
            def minus : (a:Int) -> (b:Int) -> Int = \\x -> \\y -> x - y;
            @minimize_int( year - (synth 7) )
            def synth(a: Int) : Int = (?hole:Int) * a
        """
    holes = extract_target_functions(code)
    match holes:
        case [(Name("synth", _), [Name("hole", _)])]:
            pass
        case _:
            assert False, "Wrong hole identification"


def test_hole1():
    source = r"""
        def test (x:{k:Int | k > 0}) : {z:Int | z < 0} =
        ?r
    """
    holes = extract_target_functions(source)
    match holes:
        case [(Name("test", _), [Name("r", _)])]:
            pass
        case _:
            assert False, "Wrong hole identification"


def test_hole2():
    source = r"""
        type Example;
        def test: Example = ?r ;
    """
    holes = extract_target_functions(source)
    match holes:
        case [(Name("test", _), [Name("r", _)])]:
            pass
        case _:
            assert False, "Wrong hole identification"


def test_hole3():
    source = r"""
        def d: Int = (?r:Int) + (?p:Int);
        def g: Int = 1;
        def e: Int = (?q:Int) + (?c:Int);
    """
    holes = extract_target_functions(source)
    match holes:
        case [(Name("d", _), [Name("r", _), Name("p")]), (Name("e", _), [Name("q", _), Name("c")])]:
            pass
        case _:
            assert False, "Wrong hole identification"


def test_get_holes_skips_implicit_refinement_placeholders():
    """``get_holes`` must not return ``ImplicitRefinementHole`` placeholders.

    Elaboration inserts these as the ``refinement`` field of
    ``RefinementApplication`` when instantiating an
    ``RefinementPolymorphism``. They are solved by Horn inference, not GP
    synthesis. Regression for #295: previously the filter relied on the
    hole's name starting with ``_pred``, which silently broke if anyone
    renamed elaboration-generated holes.
    """
    body = Var(Name("f", 0))
    implicit = ImplicitRefinementHole(Name("_pred", 1))
    user = Hole(Name("user_hole", 2))

    # Implicit placeholder is structurally distinct — recursion lands on the
    # dedicated leaf case and yields no hole names.
    assert get_holes(RefinementApplication(body, implicit)) == []
    # A user hole in the same field position is still reported.
    assert get_holes(RefinementApplication(body, user)) == [Name("user_hole", 2)]


def test_get_holes_ignores_name_prefix_for_user_holes():
    """A user hole that happens to be named ``_pred...`` must still be
    reported. The old prefix-based filter would have silently dropped it.
    """
    body = Var(Name("f", 0))
    misnamed = Hole(Name("_pred_user", 7))
    assert get_holes(RefinementApplication(body, misnamed)) == [Name("_pred_user", 7)]


def test_implicit_refinement_hole_not_a_hole_subclass():
    """``ImplicitRefinementHole`` must be a sibling, not a subclass, of
    ``Hole``. The whole point of #295's structural split is that
    ``isinstance(x, Hole)`` patterns at synthesis sites never match an
    implicit-refinement placeholder. If someone ever makes the new class
    inherit from ``Hole``, this test fires before any other consumer
    silently regresses to the old, brittle behavior.
    """
    irh = ImplicitRefinementHole(Name("_pred", 0))
    assert not isinstance(irh, Hole)
    assert not issubclass(ImplicitRefinementHole, Hole)
