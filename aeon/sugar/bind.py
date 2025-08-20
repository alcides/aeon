from typing import MutableSequence

# from loguru import logger
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
    SRefinementApplication,
    SVar,
    TypeDecl,
)
from aeon.sugar.stypes import (
    SAbstractionType,
    SRefinedType,
    SType,
    STypeConstructor,
    STypePolymorphism,
    SRefinementPolymorphism,
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
    # logger.log("AST_INFO", f"Binding type {ty}, {ty.__class__}")
    match ty:
        case STypeVar(name):
            return STypeVar(apply_subs_name(subs, name))
        case STypeConstructor(name, args):
            nargs = [bind_stype(aty, subs) for aty in args]
            return STypeConstructor(apply_subs_name(subs, name), nargs)
        case SAbstractionType(aname, atype, rtype):
            nname, nsubs = check_name(aname, subs)

            return SAbstractionType(nname, bind_stype(atype, subs), bind_stype(rtype, nsubs))
        case SRefinedType(name, ty, ref):
            # logger.log("AST_INFO", f"Binding refined type {name}:{ty} with ref {ref}")
            nty = bind_stype(ty, subs)
            nname, nsubs = check_name(name, subs)
            nref = bind_sterm(ref, nsubs)
            # logger.log("AST_INFO", f"Bound refined type {nname}:{nty} with ref {nref}")
            return SRefinedType(nname, nty, nref)
        case STypePolymorphism(name, kind, body):
            name, subs = check_name(name, subs)
            return STypePolymorphism(name, kind, bind_stype(body, subs))
        case SRefinementPolymorphism(name, kind, body):
            name, subs = check_name(name, subs)
            return SRefinementPolymorphism(name, kind, bind_stype(body, subs))
        case _:
            assert False, f"Unique not supported for {ty} ({type(ty)})"


def bind_sterm(t: STerm, subs: RenamingSubstitions) -> STerm:
    # logger.log("AST_INFO", f"Binding term {t}, {t.__class__}")
    match t:
        case SLiteral(_, _):
            return t
        case SVar(name):
            # logger.log("AST_INFO", f"Binding variable {name}")
            name, _ = check_name(name, subs)
            # logger.log("AST_INFO", f"Bound variable {name}")
            return SVar(name)
        case SHole(name):
            name, _ = check_name(name, subs)
            return SHole(name)
        case SAnnotation(e, ty):
            return SAnnotation(bind_sterm(e, subs), bind_stype(ty, subs))
        case SApplication(e1, e2):
            # logger.log("AST_INFO", f"Binding application {e1} {e2}")
            fun = bind_sterm(e1, subs)
            arg = bind_sterm(e2, subs)
            # logger.log("AST_INFO", f"Bound application {fun} {arg}")
            return SApplication(fun, arg)
        case SAbstraction(name, body):
            name, subs = check_name(name, subs)
            nbody = bind_sterm(body, subs)
            return SAbstraction(name, nbody)
        case STypeApplication(body, ty):
            # logger.log("AST_INFO", f"Binding type application {body} with type {ty}")
            ty = bind_stype(ty, subs)
            body = bind_sterm(body, subs)
            # logger.log("AST_INFO", f"Bound type application {body} with type {ty}")
            return STypeApplication(body, ty)
        case SRefinementApplication(body, ty):
            ty = bind_stype(ty, subs)
            body = bind_sterm(body, subs)
            return SRefinementApplication(body, ty)
        case STypeAbstraction(name, kind, body):
            name, subs = check_name(name, subs)
            return STypeAbstraction(name, kind, bind_sterm(body, subs))
        case SIf(cond, then, otherwise):
            return SIf(bind_sterm(cond, subs), bind_sterm(then, subs), bind_sterm(otherwise, subs))
        case SLet(name, body, cont):
            name, nsubs = check_name(name, subs)
            return SLet(name, bind_sterm(body, subs), bind_sterm(cont, nsubs))
        case SRec(name, ty, body, cont):
            name, subs = check_name(name, subs)
            return SRec(name, bind_stype(ty, subs), bind_sterm(body, subs), bind_sterm(cont, subs))
        case _:
            assert False, f"Unique not supported for {t} ({type(t)})"


def bind_program(p: Program, subs: RenamingSubstitions) -> Program:
    type_decls = []
    definitions = []
    nsubs = list(subs)
    # logger.log("AST_INFO",f"Binding program \n {p}")
    for td in p.type_decls:
        # logger.log("AST_INFO",f"Binding type decl {td}")
        name, nsubs = check_name(td.name, nsubs)
        type_decls.append(TypeDecl(name, td.args))
    for df in p.definitions:
        # logger.log("AST_INFO",f"Binding definition {df}")
        name, nsubs = check_name(df.name, nsubs)
        foralls = []
        for name, kind in df.foralls:
            # logger.log("AST_INFO",f"Binding forall {name} : {kind}")
            nname, nsubs = check_name(name, nsubs)
            # logger.log("AST_INFO",f"Bound forall {nname} : {kind}")
            foralls.append((nname, kind))
        rforalls = []
        for name, type in df.rforalls:
            # logger.log("AST_INFO", f"Binding rforall {name} : {ty}")
            nname, nsubs = check_name(name, nsubs)
            # logger.log("AST_INFO", f"Bound rforall {nname} : {nty}")
            rforalls.append((nname, type))
        args = []
        for aname, ty in df.args:
            # logger.log("AST_INFO",f"Binding arg {aname} : {ty}")
            nname, nsubs = check_name(aname, nsubs)
            ty = bind_stype(ty, nsubs)
            # logger.log("AST_INFO",f"Bound arg {nname} : {ty}")
            args.append((nname, ty))
        ntype = bind_stype(df.type, nsubs)
        body = bind_sterm(df.body, nsubs)
        decorators = []
        for dec in df.decorators:
            dargs = []
            # logger.log("AST_INFO", f"Binding decorator {dec.name} with args {dec.macro_args}")
            for da in dec.macro_args:
                dargs.append(bind_sterm(da, subs))
            # logger.log("AST_INFO", f"Bound decorator {dec.name} with args {dargs}")
            decorators.append(Decorator(dec.name, dargs))
        d = Definition(name, foralls, rforalls, args, ntype, body, decorators)
        # logger.log("AST_INFO", f"Bound definition {d}")
        definitions.append(d)
    return Program(p.imports, type_decls, [], definitions)


def bind(ectx: ElaborationTypingContext, s: STerm) -> tuple[ElaborationTypingContext, STerm]:
    subs: RenamingSubstitions = []
    # logger.log("AST_INFO", f"Binding term {s} with context {ectx}")
    # logger.log("AST_INFO", f"Binding context {ectx}")
    ectx, subs = bind_ectx(ectx, subs)
    # logger.log("AST_INFO", f"Bound context {ectx}")
    term = bind_sterm(s, subs)
    # logger.log("AST_INFO", f"Bound term {term}")
    return ectx, term
