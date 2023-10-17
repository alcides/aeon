from aeon.core.types import top
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.typechecking.elaboration import elaborate
from aeon.typechecking.typeinfer import check_type, check_type_errors


def check_sugar(source, ty, res):
    p = parse_program(source)
    p, ctx, ectx = desugar(p)
    p2 = elaborate(ctx, p)
    print(p2)
    print(check_type_errors(ctx, p2, ty))
    assert check_type(ctx, p2, ty)
    assert eval(p2, ectx) == res


def test_double_forall():
    source = r"""
    type Tuple x:B,y:B;
    def fun : forall a:B, forall b:B, (x:a) -> (y:b) -> Tuple [a, b] = native "lambda x: lambda y: (x,y)";
    def r : Tuple [Int, Float] = fun 3 3.0; def main : (x:Int) -> Top = \x -> r; """

    check_sugar(source, top, (3, 3.0))
