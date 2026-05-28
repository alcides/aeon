from aeon.core.terms import Hole, RefinementApplication, Var
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
    """``get_holes`` must skip ``RefinementApplication`` refinement positions
    when the inner ``Hole`` carries the ``is_implicit_refinement`` flag.

    These placeholders are inserted by elaboration when instantiating an
    ``RefinementPolymorphism`` and are solved by Horn inference, not GP.
    Regression for #295: previously the filter relied on the hole's name
    starting with the ``_pred`` prefix, which is brittle to renames.
    """
    body = Var(Name("f", 0))
    implicit = Hole(Name("_pred", 1), is_implicit_refinement=True)
    user = Hole(Name("user_hole", 2))

    # Implicit refinement placeholder is filtered out — only the body is walked.
    assert get_holes(RefinementApplication(body, implicit)) == []
    # A user hole in the same position is still reported.
    assert get_holes(RefinementApplication(body, user)) == [Name("user_hole", 2)]


def test_get_holes_ignores_name_prefix_for_user_holes():
    """A user-written hole that happens to be named ``_pred*`` must still be
    reported. The old prefix-based check would have silently dropped it;
    after #295 only the typed marker matters.
    """
    body = Var(Name("f", 0))
    misnamed = Hole(Name("_pred_user", 7), is_implicit_refinement=False)
    assert get_holes(RefinementApplication(body, misnamed)) == [Name("_pred_user", 7)]
