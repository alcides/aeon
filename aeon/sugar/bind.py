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
    InductiveDecl,
    Program,
    SAbstraction,
    SAnnotation,
    SApplication,
    SHole,
    SIf,
    SMatch,
    SLet,
    SLiteral,
    SRec,
    SRefinementAbstraction,
    SRefinementApplication,
    STerm,
    STypeAbstraction,
    STypeApplication,
    SVar,
    TypeDecl,
)
from aeon.sugar.stypes import (
    SAbstractionType,
    SRefinedType,
    SRefinementPolymorphism,
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
        case STypeVar(name):
            return STypeVar(apply_subs_name(subs, name))
        case STypeConstructor(name, args):
            nargs = [bind_stype(aty, subs) for aty in args]
            return STypeConstructor(apply_subs_name(subs, name), nargs)
        case SAbstractionType(aname, atype, rtype):
            nname, nsubs = check_name(aname, subs)

            return SAbstractionType(nname, bind_stype(atype, subs), bind_stype(rtype, nsubs))
        case SRefinedType(name, ty, ref):
            nty = bind_stype(ty, subs)
            nname, nsubs = check_name(name, subs)
            nref = bind_sterm(ref, nsubs)
            return SRefinedType(nname, nty, nref)
        case STypePolymorphism(name, kind, body):
            name, subs = check_name(name, subs)
            return STypePolymorphism(name, kind, bind_stype(body, subs))
        case SRefinementPolymorphism(name, sort, body):
            bound_sort = bind_stype(sort, subs)
            nname, nsubs = check_name(name, subs)
            return SRefinementPolymorphism(nname, bound_sort, bind_stype(body, nsubs))
        case _:
            assert False, f"Unique not supported for {ty} ({type(ty)})"


def bind_sterm(t: STerm, subs: RenamingSubstitions) -> STerm:
    match t:
        case SLiteral(_, _):
            return t
        case SVar(name, loc=loc):
            return SVar(apply_subs_name(subs, name), loc=loc)
        case SHole(name, loc=loc):
            name, _ = check_name(name, subs)
            return SHole(name, loc=loc)
        case SAnnotation(e, ty, loc=loc):
            return SAnnotation(bind_sterm(e, subs), bind_stype(ty, subs), loc=loc)
        case SApplication(e1, e2, loc=loc):
            return SApplication(bind_sterm(e1, subs), bind_sterm(e2, subs), loc=loc)
        case SAbstraction(name, body, loc=loc):
            name, subs = check_name(name, subs)
            nbody = bind_sterm(body, subs)
            return SAbstraction(name, nbody, loc=loc)
        case STypeApplication(body, ty, loc=loc):
            return STypeApplication(bind_sterm(body, subs), bind_stype(ty, subs), loc=loc)
        case SRefinementApplication(body, refinement, loc=loc):
            return SRefinementApplication(bind_sterm(body, subs), bind_sterm(refinement, subs), loc=loc)
        case STypeAbstraction(name, kind, body, loc=loc):
            name, subs = check_name(name, subs)
            return STypeAbstraction(name, kind, bind_sterm(body, subs), loc=loc)
        case SRefinementAbstraction(name, sort, body, loc=loc):
            name, subs = check_name(name, subs)
            return SRefinementAbstraction(name, bind_stype(sort, subs), bind_sterm(body, subs), loc=loc)
        case SIf(cond, then, otherwise, loc=loc):
            return SIf(bind_sterm(cond, subs), bind_sterm(then, subs), bind_sterm(otherwise, subs), loc=loc)
        case SMatch(scrutinee, branches, loc=loc):
            n_scrutinee = bind_sterm(scrutinee, subs)
            n_branches = []
            # Pattern binders are scoped to each match branch.
            for br in branches:
                branch_subs = list(subs)
                renamed_binders: list[Name] = []
                for b in br.binders:
                    nb, branch_subs = check_name(b, branch_subs)
                    renamed_binders.append(nb)
                n_body = bind_sterm(br.body, branch_subs)
                # Align pattern constructor names with the `Name` ids assigned while
                # binding inductive constructor definitions (see `bind_program`).
                ctor = apply_subs_name(subs, br.constructor)
                n_branches.append(type(br)(constructor=ctor, binders=renamed_binders, body=n_body, loc=br.loc))
            return SMatch(n_scrutinee, n_branches, loc=loc)
        case SLet(name, body, cont, loc=loc):
            name, nsubs = check_name(name, subs)
            return SLet(name, bind_sterm(body, subs), bind_sterm(cont, nsubs), loc=loc)
        case SRec(name, ty, body, cont, decreasing_by, loc=loc):
            name, subs = check_name(name, subs)
            nd = tuple(bind_sterm(m, subs) for m in decreasing_by)
            return SRec(
                name, bind_stype(ty, subs), bind_sterm(body, subs), bind_sterm(cont, subs), decreasing_by=nd, loc=loc
            )
        case _:
            assert False, f"Unique not supported for {t} ({type(t)})"


def _bind_definition(
    df: Definition, nsubs: RenamingSubstitions, subs: RenamingSubstitions
) -> tuple[Definition, RenamingSubstitions]:
    name, nsubs = check_name(df.name, nsubs)
    foralls = []
    for fname, kind in df.foralls:
        nname, nsubs = check_name(fname, nsubs)
        foralls.append((nname, kind))
    args = []
    for aname, ty in df.args:
        nname, nsubs = check_name(aname, nsubs)
        ty = bind_stype(ty, nsubs)
        args.append((nname, ty))
    rforalls = []
    for pname, psort in df.rforalls:
        nname, nsubs = check_name(pname, nsubs)
        rforalls.append((nname, bind_stype(psort, nsubs)))
    ntype = bind_stype(df.type, nsubs)
    decreasing = [bind_sterm(m, nsubs) for m in df.decreasing_by]
    body = bind_sterm(df.body, nsubs)
    decorators = []
    for dec in df.decorators:
        dargs = [bind_sterm(da, subs) for da in dec.macro_args]
        decorators.append(Decorator(dec.name, dargs))
    return Definition(
        name, foralls, args, ntype, body, decorators, rforalls, decreasing_by=decreasing, loc=df.loc
    ), nsubs


def bind_program(p: Program, subs: RenamingSubstitions) -> Program:
    type_decls = []
    inductive_decls = []
    definitions = []
    nsubs = list(subs)

    # Register all declared type names first so they are treated as concrete
    # types (not free type variables) throughout the rest of the program.
    for td in p.type_decls:
        name, nsubs = check_name(td.name, nsubs)
        type_decls.append(TypeDecl(name, td.args, loc=td.loc))
    for ind in p.inductive_decls:
        name, nsubs = check_name(ind.name, nsubs)
        iargs = []
        for aname in ind.args:
            nname, nsubs = check_name(aname, nsubs)
            iargs.append(nname)
        constructors = []
        for cons in ind.constructors:
            bound_cons, nsubs = _bind_definition(cons, nsubs, subs)
            constructors.append(bound_cons)
        measures = []
        for meas in ind.measures:
            bound_meas, nsubs = _bind_definition(meas, nsubs, subs)
            measures.append(bound_meas)
        inductive_decls.append(InductiveDecl(name, iargs, constructors, measures, loc=ind.loc))

    for df in p.definitions:
        bound_df, nsubs = _bind_definition(df, nsubs, subs)
        definitions.append(bound_df)

    return Program(p.imports, type_decls, inductive_decls, definitions)


def bind(ectx: ElaborationTypingContext, s: STerm) -> tuple[ElaborationTypingContext, STerm]:
    subs: RenamingSubstitions = []
    ectx, subs = bind_ectx(ectx, subs)
    return ectx, bind_sterm(s, subs)
