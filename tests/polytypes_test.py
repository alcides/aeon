from aeon.core.liquid import LiquidLiteralBool
from aeon.core.types import TypeConstructor
from aeon.frontend.parser import parse_type
from aeon.logger.logger import setup_logger
from aeon.typechecking.context import TypingContext
from aeon.verification.sub import sub
from aeon.verification.vcs import LiquidConstraint
from aeon.sugar.parser import parse_program
from aeon.sugar.program import Program
from aeon.sugar.desugar import desugar
from aeon.typechecking.typeinfer import check_type_errors
from aeon.core.types import top

setup_logger()


def sugar_test_pipeline(code: str, fail: bool = False):
    prog: Program = parse_program(code)
    term, ctx, ectx = desugar(prog)
    assert check_type_errors(ctx, term, top) != fail


def test_polytype():
    ctx = TypingContext()
    t = parse_type("List[Int]")
    assert isinstance(t, TypeConstructor)

    t2 = parse_type("List[Int]")
    assert sub(ctx, t, t2)

    t3 = parse_type("List[Float]")
    assert sub(ctx, t, t3) == LiquidConstraint(LiquidLiteralBool(False))


def test_polyfun():
    sugar_test_pipeline(
        """
    type List a:B;
    def empty : forall a:B, List[a] = native "[]";
    def append : forall a:B, (li: List[a]) -> (element : a ) -> {li : List[a] | true} = native "lambda li: lambda element: [ e for e in li ] + [element]";
    def main() : Top {
        a : List[Bool] = empty[Bool];
        b : List[Int] = empty;
        c : List[Int] = append b 3;
        d : List[Int] = append a 3; # Should be an error
        a
    }
                      """,
        fail=True,
    )

    sugar_test_pipeline(
        """
    type List a:B;
    def empty : forall a:B, List[a] = native "[]";
    def append : forall a:B, (li: List[a]) -> (element : a ) -> {li : List[a] | true} = native "lambda li: lambda element: [ e for e in li ] + [element]";
    def main() : Top {
        a : List[Bool] = empty[Bool];
        b : List[Int] = empty;
        c : List[Int] = append b 3;
        a
    }
                      """,
    )
