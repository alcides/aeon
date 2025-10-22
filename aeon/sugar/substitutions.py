from aeon.utils.name import Name
from aeon.sugar.stypes import (
    SAbstractionType,
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
            new_ref = SApplication(SApplication(SVar(Name("&&", 0)), a1), oref)
            return SRefinedType(oname, ity, new_ref)
        case _:
            return ty


def substitute_svartype_in_stype(ty: SType, beta: SType, alpha: Name):
    """Replaces all occurrences of vartypes name in t by rep."""

    def rec(k: SType):
        return substitute_svartype_in_stype(k, beta, alpha)

    ty = normalize(ty)
    match ty:
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


def substitution_sterm_in_stype(ty: SType, beta: STerm, alpha: Name) -> SType:
    def rec(k: SType):
        return substitution_sterm_in_stype(k, beta, alpha)

    match ty:
        case STypeVar(_):
            return ty
        case SRefinedType(name, ty, ref):
            return SRefinedType(name, rec(ty), substitution_sterm_in_sterm(ref, beta, alpha))
        case SAbstractionType(var_name, var_type, return_type):
            return SAbstractionType(var_name, rec(var_type), rec(return_type))
        case STypePolymorphism(tname, kind, body):
            return STypePolymorphism(tname, kind, rec(body))
        case STypeConstructor(name, args):
            return STypeConstructor(name, [rec(a) for a in args])
        case _:
            assert False


def substitution_sterm_in_sterm(t: STerm, beta: STerm, alpha: Name) -> STerm:
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
        case SApplication(fun, arg, loc):
            return SApplication(rec(fun), rec(arg), loc=loc)
        case SAbstraction(aname, body, loc):
            if aname == alpha:
                return t
            else:
                return SAbstraction(aname, rec(body), loc=loc)
        case SLet(vname, vvalue, body, loc):
            if vname == alpha:
                return SLet(vname, rec(vvalue), body, loc=loc)
            else:
                return SLet(vname, rec(vvalue), rec(body), loc=loc)
        case SRec(vname, vty, vvalue, body, loc):
            if vname == alpha:
                return SRec(vname, rect(vty), rec(vvalue), body, loc=loc)
            else:
                return SRec(vname, rect(vty), rec(vvalue), rec(body), loc=loc)
        case SAnnotation(expr, ty, loc):
            return SAnnotation(rec(expr), rect(ty), loc=loc)
        case SIf(cond, then, otherwise, loc):
            return SIf(rec(cond), rec(then), rec(otherwise), loc=loc)
        case STypeApplication(body, ty, loc):
            return STypeApplication(rec(body), rect(ty), loc=loc)
        case STypeAbstraction(aname, kind, body, loc):
            return STypeAbstraction(aname, kind, rec(body), loc=loc)
        case _:
            assert False


def substitution_svartype_in_sterm(t: STerm, rep: SType, name: Name) -> STerm:
    def rec(x: STerm):
        return substitution_svartype_in_sterm(x, rep, name)

    match t:
        case SVar(_) | SHole(_):
            return t
        case SLiteral(v, ty, loc):
            return SLiteral(v, substitute_svartype_in_stype(ty, rep, name), loc=loc)
        case SApplication(fun, arg, loc):
            return SApplication(rec(fun), rec(arg), loc=loc)
        case SAbstraction(aname, body, loc):
            return SAbstraction(aname, rec(body), loc=loc)
        case SLet(vname, vvalue, body, loc):
            return SLet(vname, rec(vvalue), rec(body), loc=loc)
        case SRec(vname, vtype, vvalue, body, loc):
            return SRec(vname, substitute_svartype_in_stype(vtype, rep, name), rec(vvalue), rec(body), loc=loc)
        case SAnnotation(expr, ty, loc):
            return SAnnotation(rec(expr), substitute_svartype_in_stype(ty, rep, name), loc=loc)
        case SIf(cond, then, otherwise, loc):
            return SIf(rec(cond), rec(then), rec(otherwise), loc=loc)
        case STypeApplication(body, ty, loc):
            return STypeApplication(rec(body), substitute_svartype_in_stype(ty, rep, name), loc=loc)
        case STypeAbstraction(aname, kind, body, loc):
            if aname == name:
                return t
            else:
                return STypeAbstraction(aname, kind, rec(body), loc=loc)
        case _:
            assert False
