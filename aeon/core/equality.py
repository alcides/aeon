from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralFloat,
    LiquidLiteralInt,
    LiquidLiteralString,
    LiquidTerm,
    LiquidVar,
)
from aeon.utils.name import Name
from aeon.core.terms import Term, Literal, Var, Application, Abstraction, Let, Rec, If, TypeAbstraction, TypeApplication
from aeon.core.types import (
    LiquidHornApplication,
    Type,
    BaseType,
    TypeVar,
    AbstractionType,
    RefinedType,
    TypePolymorphism,
    TypeConstructor,
    Top,
)


def debug(f):
    def g(a, b, *others):
        v = f(a, b, *others)
        print("a:", a)
        print("b:", b)
        print(others)
        print("->", v)
        return v

    return g


@debug
def core_liquid_equality(lq1: LiquidTerm, lq2: LiquidTerm, rename_left: dict[Name, Name] | None = None) -> bool:
    "Equality of liquid terms up to alpha renaming"
    rename_left = rename_left or {}
    match lq1, lq2:
        case LiquidVar(an), LiquidVar(bn):
            return rename_left.get(an, an) == bn
        case LiquidLiteralBool(a), LiquidLiteralBool(b):
            return a == b
        case LiquidLiteralInt(a), LiquidLiteralInt(b):
            return a == b
        case LiquidLiteralFloat(a), LiquidLiteralFloat(b):
            return a == b
        case LiquidLiteralString(a), LiquidLiteralString(b):
            return a == b
        case LiquidApp(a1, a2), LiquidApp(b1, b2):
            return a1 == b1 and all(core_liquid_equality(i2, j2, rename_left) for (i2, j2) in zip(a2, b2))
        case LiquidHornApplication(a1, _), LiquidHornApplication(b1, _):
            return a1 == b1
        case _:
            return False


@debug
def core_type_equality(type1: Type, type2: Type, rename_left: dict[Name, Name] | None = None) -> bool:
    "Equality of types up to alpha renaming"
    rename_left = rename_left or {}
    match type1, type2:
        case TypeVar(an), TypeVar(bn):
            return rename_left.get(an, an) == bn
        case BaseType(av), BaseType(bv):
            return av == bv
        case RefinedType(aname, aty, aref), RefinedType(bname, bty, bref):
            return core_type_equality(aty, bty, rename_left) and core_liquid_equality(
                aref, bref, rename_left | {aname: bname}
            )
        case AbstractionType(aname, a1, a2), AbstractionType(bname, b1, b2):
            return core_type_equality(a1, b1, rename_left) and core_type_equality(a2, b2, rename_left | {aname: bname})
        case TypeConstructor(aname, a1), TypeConstructor(bname, b1):
            return aname == bname and all(core_type_equality(a, b, rename_left) for a, b in zip(a1, b1))
        case TypePolymorphism(aname, akind, abody), TypePolymorphism(bname, bkind, bbody):
            return akind == bkind and core_type_equality(abody, bbody, rename_left | {aname: bname})
        case Top(), Top():
            return True
        case _:
            return False


def core_term_equality(term1: Term, term2: Term, rename_left: dict[Name, Name] | None = None) -> bool:
    "Equality of terms up to alpha renaming"
    rename_left = rename_left or {}
    match term1, term2:
        case Var(an), Var(bn):
            return rename_left.get(an, an) == bn
        case Literal(av, at), Literal(bv, bt):
            return av == bv and core_type_equality(at, bt, rename_left)
        case Application(a1, a2), Application(b1, b2):
            return core_term_equality(a1, b1, rename_left) and core_term_equality(a2, b2, rename_left)
        case Abstraction(an, abody), Abstraction(bn, bbody):
            return core_term_equality(abody, bbody, rename_left | {an: bn})
        case Let(aname, aval, acont), Let(bname, bval, bcont):
            return core_term_equality(aval, bval, rename_left) and core_term_equality(
                acont, bcont, rename_left | {aname: bname}
            )
        case Rec(aname, atype, aval, acont), Rec(bname, btype, bval, bcont):
            nrename = rename_left | {aname: bname}
            return (
                core_term_equality(aval, bval, nrename)
                and core_type_equality(atype, btype, rename_left)
                and core_term_equality(acont, bcont, nrename)
            )
        case If(ac, at, ao), If(bc, bt, bo):
            return (
                core_term_equality(ac, bc, rename_left)
                and core_term_equality(at, bt, rename_left)
                and core_term_equality(ao, bo, rename_left)
            )
        case TypeApplication(ab, at), TypeApplication(bb, bt):
            return core_term_equality(ab, bb, rename_left) and core_type_equality(at, bt, rename_left)
        case TypeAbstraction(aname, akind, abody), TypeAbstraction(bname, bkind, bbody):
            return akind == bkind and core_term_equality(abody, bbody, rename_left | {aname: bname})
        case _:
            return False
