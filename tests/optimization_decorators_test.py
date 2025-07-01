from aeon.synthesis.identification import iterate_top_level
from aeon.sugar.ast_helpers import st_top

from tests.driver import check_compile, extract_core


def test_hole_minimize_int():
    code = """
            def year : Int = 2023;
            def minus : (a:Int) -> (b:Int) -> Int = \\x -> \\y -> x - y;
            @minimize_int( year - (synth 7) )
            def synth(a: Int) : Int { (?hole:Int) * a}
        """
    core = extract_core(code)
    assert len(list(iterate_top_level(core))) == 3 + 1


def test_eq() -> None:
    aeon_code = """
        def main(args:Int) : Unit {
            x : String = "ola";
            x1 : String = x;
            x2 : String = x;
            z3 : Bool = x1 == x2;
            print z3
        }"""

    check_compile(aeon_code, st_top)
