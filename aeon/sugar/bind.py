from typing import MutableSequence
from aeon.elaboration.context import (
    ElabTypingContextEntry,
    ElabVariableBinder,
    ElaborationTypingContext,
    ElabUninterpretedBinder,
    ElabTypeVarBinder,
    ElabTypeDecl,
)
from aeon.sugar.program import (
    Decorator,
    Definition,
    Program,
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
    TypeDecl,
)
from aeon.sugar.stypes import (
    SAbstractionType,
    SRefinedType,
    SType,
    STypeConstructor,
    STypePolymorphism,
    STypeVar,
)
from aeon.utils.name import Name, fresh_counter

RenamingSubstitions = list[tuple[str, Name]]


def get_last_id(x: str, subs: RenamingSubstitions) -> Name | None:
    for sub, v in subs[::-1]:
        if x == sub:
            return v
    return None


def check_name(name: Name, subs: RenamingSubstitions) -> tuple[Name, RenamingSubstitions]:
    if name.id == -1:
        nname = Name(name.name, fresh_counter.fresh())
        return nname, subs + [(name.name, nname)]
    else:
        return name, subs + [(name.name, name)]


def apply_subs_name(subs: RenamingSubstitions, name: Name) -> Name:
    for sub, v in subs[::-1]:
        if sub == name.name:
            return v
    return name


def bind_ectx(
    ectx: ElaborationTypingContext, subs: RenamingSubstitions
) -> tuple[ElaborationTypingContext, RenamingSubstitions]:
    nentries: MutableSequence[ElabTypingContextEntry] = []
    for entry in ectx.entries:
        e: ElabTypingContextEntry
        match entry:
            case ElabVariableBinder(name, stype):
                name, subs = check_name(name, subs)
                e = ElabVariableBinder(name, bind_stype(stype, subs))
            case ElabUninterpretedBinder(name, stype):
                name, subs = check_name(name, subs)
                e = ElabUninterpretedBinder(name, bind_stype(stype, subs))
            case ElabTypeVarBinder(name, kind):
                name, subs = check_name(name, subs)
                e = ElabTypeVarBinder(name, kind)
            case ElabTypeDecl(name, args):
                name, subs = check_name(name, subs)
                e = ElabTypeDecl(name, args)
            case _:
                assert False, f"{entry} not yet supported in bind."
        nentries.append(e)
    return ElaborationTypingContext(nentries), subs


def bind_stype(ty: SType, subs: RenamingSubstitions) -> SType:
    match ty:
        case STypeVar(name, loc):
            return STypeVar(apply_subs_name(subs, name), loc)
        case STypeConstructor(name, args, loc):
            nargs = [bind_stype(aty, subs) for aty in args]
            return STypeConstructor(apply_subs_name(subs, name), nargs, loc)
        case SAbstractionType(aname, atype, rtype, loc):
            nname, nsubs = check_name(aname, subs)
            return SAbstractionType(nname, bind_stype(atype, subs), bind_stype(rtype, nsubs), loc)
        case SRefinedType(name, ty_inner, ref, loc):
            nty = bind_stype(ty_inner, subs)
            nname, nsubs = check_name(name, subs)
            nref = bind_sterm(ref, nsubs)
            return SRefinedType(nname, nty, nref, loc)
        case STypePolymorphism(name, kind, body, loc):
            name, subs = check_name(name, subs)
            return STypePolymorphism(name, kind, bind_stype(body, subs), loc)
        case _:
            assert False, f"Unique not supported for {ty} ({type(ty)})"


def bind_sterm(t: STerm, subs: RenamingSubstitions) -> STerm:
    match t:
        case SLiteral(_, _):
            return t
        case SVar(name, loc):
            return SVar(apply_subs_name(subs, name), loc)
        case SHole(name, loc):
            name, _ = check_name(name, subs)
            return SHole(name, loc)
        case SAnnotation(e, ty, loc):
            return SAnnotation(bind_sterm(e, subs), bind_stype(ty, subs), loc)
        case SApplication(e1, e2, loc):
            return SApplication(bind_sterm(e1, subs), bind_sterm(e2, subs), loc)
        case SAbstraction(name, body, loc):
            name, subs = check_name(name, subs)
            return SAbstraction(name, bind_sterm(body, subs), loc)
        case STypeApplication(body, ty, loc):
            return STypeApplication(bind_sterm(body, subs), bind_stype(ty, subs), loc)
        case STypeAbstraction(name, kind, body, loc):
            name, subs = check_name(name, subs)
            return STypeAbstraction(name, kind, bind_sterm(body, subs), loc)
        case SIf(cond, then, otherwise, loc):
            return SIf(bind_sterm(cond, subs), bind_sterm(then, subs), bind_sterm(otherwise, subs), loc)
        case SLet(name, body, cont, loc):
            name, nsubs = check_name(name, subs)
            return SLet(name, bind_sterm(body, subs), bind_sterm(cont, nsubs), loc)
        case SRec(name, ty, body, cont, loc):
            name, subs = check_name(name, subs)
            return SRec(name, bind_stype(ty, subs), bind_sterm(body, subs), bind_sterm(cont, subs), loc)
        case _:
            assert False, f"Unique not supported for {t} ({type(t)})"


def bind_program(p: Program, subs: RenamingSubstitions) -> Program:
    type_decls = []
    definitions = []
    nsubs = list(subs)
    for td in p.type_decls:
        name, nsubs = check_name(td.name, nsubs)
        type_decls.append(TypeDecl(name, td.args, td.loc))
    for df in p.definitions:
        name, nsubs = check_name(df.name, nsubs)
        foralls = []
        for name, kind in df.foralls:
            nname, nsubs = check_name(name, nsubs)
            foralls.append((nname, kind))
        args = []
        for aname, ty in df.args:
            nname, nsubs = check_name(aname, nsubs)
            ty = bind_stype(ty, nsubs)
            args.append((nname, ty))
        ntype = bind_stype(df.type, nsubs)
        body = bind_sterm(df.body, nsubs)
        decorators = []
        for dec in df.decorators:
            dargs = []
            for da in dec.macro_args:
                dargs.append(bind_sterm(da, subs))
            decorators.append(Decorator(dec.name, dargs))
        d = Definition(name, foralls, args, ntype, body, decorators, df.loc)
        definitions.append(d)
    return Program(p.imports, type_decls, [], definitions)


def bind(ectx: ElaborationTypingContext, s: STerm) -> tuple[ElaborationTypingContext, STerm]:
    subs: RenamingSubstitions = []
    ectx, subs = bind_ectx(ectx, subs)
    return ectx, bind_sterm(s, subs)
