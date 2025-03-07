from aeon.sugar.stypes import (
    SAbstractionType,
    SBaseType,
    STypeConstructor,
    STypeVar,
    SRefinedType,
    SType,
    STypePolymorphism,
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


def normalize(ty: SType) -> SType:
    match ty:
        case SRefinedType(oname, SRefinedType(iname, ity, iref), oref):
            a1 = substitution_sterm_in_sterm(
                iref,
                SVar(oname),
                iname,
            )
            new_ref = SApplication(SApplication(SVar("&&"), a1), oref)
            return SRefinedType(oname, ity, new_ref)
        case _:
            return ty


def substitute_svartype_in_stype(ty: SType, beta: SType, alpha: str):
    """Replaces all occurrences of vartypes name in t by rep."""

    def rec(k: SType):
        return substitute_svartype_in_stype(k, beta, alpha)

    ty = normalize(ty)
    match ty:
        case SBaseType(_):
            return ty
        case STypeVar(tname):
            if tname == alpha:
                return beta
            else:
                return ty
        case SRefinedType(name, ty, ref):
            return SRefinedType(name, rec(ty), ref)
        case SAbstractionType(var_name, var_type, return_type):
            return SAbstractionType(var_name, rec(var_type), rec(return_type))
        case STypePolymorphism(tname, kind, body):
            if tname == alpha:
                return ty
            else:
                return STypePolymorphism(tname, kind, rec(body))
        case STypeConstructor(name, args):
            return STypeConstructor(name, [rec(a) for a in args])
        case _:
            assert False, f"Unknown node in substitute {ty}"


def substitution_sterm_in_stype(ty: SType, beta: STerm, alpha: str) -> SType:

    def rec(k: SType):
        return substitution_sterm_in_stype(k, beta, alpha)

    match ty:
        case SBaseType(_) | STypeVar(_):
            return ty
        case SRefinedType(name, ty, ref):
            return SRefinedType(name, rec(ty),
                                substitution_sterm_in_sterm(ref, beta, alpha))
        case SAbstractionType(var_name, var_type, return_type):
            return SAbstractionType(var_name, rec(var_type), rec(return_type))
        case STypePolymorphism(tname, kind, body):
            return STypePolymorphism(tname, kind, rec(body))
        case STypeConstructor(name, args):
            return STypeConstructor(name, [rec(a) for a in args])
        case _:
            assert False


def substitution_sterm_in_sterm(t: STerm, beta: STerm, alpha: str) -> STerm:

    def rec(x: STerm):
        return substitution_sterm_in_sterm(x, beta, alpha)

    def rect(x: SType):
        return substitution_sterm_in_stype(x, beta, alpha)

    match t:
        case SLiteral(_, _) | SHole(_):
            return t
        case SVar(name):
            if name == alpha:
                return beta
            else:
                return t
        case SApplication(fun, arg):
            return SApplication(rec(fun), rec(arg))
        case SAbstraction(aname, body):
            if aname == alpha:
                return t
            else:
                return SAbstraction(aname, rec(body))
        case SLet(vname, vvalue, body):
            if vname == alpha:
                return SLet(vname, rec(vvalue), body)
            else:
                return SLet(vname, rec(vvalue), rec(body))
        case SRec(vname, vty, vvalue, body):
            if vname == alpha:
                return SRec(vname, rect(vty), rec(vvalue), body)
            else:
                return SRec(vname, rect(vty), rec(vvalue), rec(body))
        case SAnnotation(expr, ty):
            return SAnnotation(rec(expr), rect(ty))
        case SIf(cond, then, otherwise):
            return SIf(rec(cond), rec(then), rec(otherwise))
        case STypeApplication(body, ty):
            return STypeApplication(rec(body), rect(ty))
        case STypeAbstraction(aname, kind, body):
            return STypeAbstraction(aname, kind, rec(body))
        case _:
            assert False


def substitution_svartype_in_sterm(t: STerm, rep: SType, name: str) -> STerm:

    def rec(x: STerm):
        return substitution_svartype_in_sterm(x, rep, name)

    match t:
        case SVar(_) | SHole(_):
            return t
        case SLiteral(v, ty):
            return SLiteral(v, substitute_svartype_in_stype(ty, rep, name))
        case SApplication(fun, arg):
            return SApplication(rec(fun), rec(arg))
        case SAbstraction(aname, body):
            return SAbstraction(aname, rec(body))
        case SLet(vname, vvalue, body):
            return SLet(vname, rec(vvalue), rec(body))
        case SRec(vname, vtype, vvalue, body):
            return SRec(vname, substitute_svartype_in_stype(vtype, rep, name),
                        rec(vvalue), rec(body))
        case SAnnotation(expr, ty):
            return SAnnotation(rec(expr),
                               substitute_svartype_in_stype(ty, rep, name))
        case SIf(cond, then, otherwise):
            return SIf(rec(cond), rec(then), rec(otherwise))
        case STypeApplication(body, ty):
            return STypeApplication(
                rec(body), substitute_svartype_in_stype(ty, rep, name))
        case STypeAbstraction(aname, kind, body):
            if aname == name:
                return t
            else:
                return STypeAbstraction(aname, kind, rec(body))
        case _:
            assert False
