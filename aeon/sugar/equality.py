from aeon.utils.name import Name
from aeon.sugar.stypes import (
    SAbstractionType,
    SRefinedType,
    SType,
    STypeConstructor,
    STypePolymorphism,
    STypeVar,
)
from aeon.sugar.program import (
    SAbstraction,
    SAnnotation,
    SApplication,
    SHole,
    SIf,
    SLet,
    SLiteral,
    SRec,
    STerm,
    STypeAbstraction,
    STypeApplication,
    SVar,
)


def type_equality(a: SType, b: SType, rename_left: dict[Name, Name] | None = None) -> bool:
    "Equality of types up to alpha renaming"
    rename_left = rename_left or {}
    match a, b:
        case STypeVar(an), STypeVar(bn):
            return rename_left.get(an, an) == bn
        case SRefinedType(aname, aty, aref), SRefinedType(bname, bty, bref):
            return type_equality(aty, bty, rename_left | {aname: bname}) and term_equality(
                aref, bref, rename_left | {aname: bname}
            )
        case SAbstractionType(aname, a1, a2), SAbstractionType(bname, b1, b2):
            return type_equality(a1, b1, rename_left) and type_equality(a2, b2, rename_left | {aname: bname})
        case STypeConstructor(aname, a1), STypeConstructor(bname, b1):
            return aname == bname and all([type_equality(a, b, rename_left) for a, b in zip(a1, b1)])
        case STypePolymorphism(aname, akind, abody), STypePolymorphism(bname, bkind, bbody):
            return akind == bkind and type_equality(abody, bbody, rename_left | {aname: bname})
        case STypeApplication(ab, at), STypeApplication(bb, bt):
            return term_equality(ab, bb, rename_left) and type_equality(at, bt, rename_left)
        case STypeAbstraction(aname, akind, abody), STypeAbstraction(bname, bkind, bbody):
            return akind == bkind and term_equality(abody, bbody, rename_left | {aname: bname})
        case _:
            return False


def term_equality(a: STerm, b: STerm, rename_left: dict[Name, Name] | None = None) -> bool:
    "Equality of terms up to alpha renaming"
    rename_left = rename_left or {}
    match a, b:
        case SVar(an), SVar(bn):
            return rename_left.get(an, an) == bn
        case SHole(an), SHole(bn):
            return rename_left.get(an, an) == bn
        case SLiteral(av, at), SLiteral(bv, bt):
            return av == bv and at == bt
        case SApplication(a1, a2), SApplication(b1, b2):
            return term_equality(a1, b1, rename_left) and term_equality(a2, b2, rename_left)
        case SAbstraction(an, abody), SAbstraction(bn, bbody):
            return term_equality(abody, bbody, rename_left | {an: bn})
        case SLet(aname, aval, acont), SLet(bname, bval, bcont):
            return term_equality(aval, bval, rename_left) and term_equality(acont, bcont, rename_left | {aname: bname})
        case SRec(aname, atype, aval, acont), SRec(bname, btype, bval, bcont):
            nrename = rename_left | {aname: bname}
            return (
                term_equality(aval, bval, nrename)
                and type_equality(atype, btype, rename_left)
                and term_equality(acont, bcont, nrename)
            )
        case SAnnotation(ae, at), SAnnotation(be, bt):
            return term_equality(ae, be, rename_left) and type_equality(at, bt, rename_left)
        case SIf(ac, at, ao), SIf(bc, bt, bo):
            return (
                term_equality(ac, bc, rename_left)
                and term_equality(at, bt, rename_left)
                and term_equality(ao, bo, rename_left)
            )
        case STypeApplication(ab, at), STypeApplication(bb, bt):
            return term_equality(ab, bb, rename_left) and type_equality(at, bt, rename_left)
        case STypeAbstraction(aname, akind, abody), STypeAbstraction(bname, bkind, bbody):
            return akind == bkind and term_equality(abody, bbody, rename_left | {aname: bname})
        case _:
            return False
