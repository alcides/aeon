from aeon.core.types import StarKind
from aeon.utils.name import Name
from aeon.sugar.equality import term_equality
from aeon.sugar.program import SAbstraction, SLiteral, SVar, SApplication, SLet, SIf, SRec, STypeAbstraction
from aeon.sugar.ast_helpers import st_int

x = Name("x")
y = Name("y")


def test_term_equality():
    assert term_equality(SVar(x), SVar(x))
    assert not term_equality(SVar(x), SVar(y))

    assert term_equality(SLiteral(3, st_int), SLiteral(3, st_int))
    assert not term_equality(SLiteral(3, st_int), SLiteral(4, st_int))

    assert term_equality(SAbstraction(x, SVar(x)), SAbstraction(x, SVar(x)))
    assert term_equality(SAbstraction(x, SVar(x)), SAbstraction(y, SVar(y)))
    assert not term_equality(SAbstraction(x, SVar(x)), SAbstraction(x, SVar(y)))

    # Additional test cases
    assert term_equality(SApplication(SVar(x), SLiteral(3, st_int)), SApplication(SVar(x), SLiteral(3, st_int)))
    assert not term_equality(SApplication(SVar(x), SLiteral(3, st_int)), SApplication(SVar(y), SLiteral(3, st_int)))

    assert term_equality(SLet(x, SLiteral(3, st_int), SVar(x)), SLet(y, SLiteral(3, st_int), SVar(y)))
    assert not term_equality(SLet(x, SLiteral(3, st_int), SVar(x)), SLet(x, SLiteral(4, st_int), SVar(x)))

    assert term_equality(
        SIf(SLiteral(1, st_int), SLiteral(2, st_int), SLiteral(3, st_int)),
        SIf(SLiteral(1, st_int), SLiteral(2, st_int), SLiteral(3, st_int)),
    )
    assert not term_equality(
        SIf(SLiteral(1, st_int), SLiteral(2, st_int), SLiteral(3, st_int)),
        SIf(SLiteral(1, st_int), SLiteral(2, st_int), SLiteral(4, st_int)),
    )

    assert term_equality(SRec(x, st_int, SLiteral(3, st_int), SVar(x)), SRec(y, st_int, SLiteral(3, st_int), SVar(y)))
    assert not term_equality(
        SRec(x, st_int, SLiteral(3, st_int), SVar(x)), SRec(x, st_int, SLiteral(4, st_int), SVar(x))
    )

    assert term_equality(STypeAbstraction(x, StarKind(), SVar(x)), STypeAbstraction(y, StarKind(), SVar(y)))
    assert not term_equality(STypeAbstraction(x, StarKind(), SVar(x)), STypeAbstraction(x, StarKind(), SVar(y)))
