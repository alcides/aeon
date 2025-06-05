from aeon.synthesis.identification import incomplete_functions_and_holes
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
            def synth(a: Int) : Int { (?hole:Int) * a}
        """
    holes = extract_target_functions(code)
    match holes:
        case [(Name("synth", _), [Name("hole", _)])]:
            pass
        case _:
            assert False, "Wrong hole identification"


def test_hole1():
    source = r"""
        def test (x:{k:Int | k > 0}) : {z:Int | z < 0} {
        ?r
        }
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
