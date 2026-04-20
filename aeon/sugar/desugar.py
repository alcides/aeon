from __future__ import annotations

import os
from dataclasses import replace
from pathlib import Path
from typing import NamedTuple

from aeon.core.types import BaseKind, Kind
from aeon.decorators import apply_decorators, Metadata
from aeon.elaboration.context import (
    ElabUninterpretedBinder,
    ElabVariableBinder,
    ElaborationTypingContext,
    ElabTypingContextEntry,
    build_typing_context,
)
from aeon.prelude.prelude import typing_vars
from aeon.sugar.parser import mk_parser
from aeon.sugar.program import (
    Definition,
    SAbstraction,
    SApplication,
    SAnnotation,
    SHole,
    SBy,
    SLiteral,
    SIf,
    SRec,
    SLet,
    SMatch,
    SMatchBranch,
    SRefinementAbstraction,
    STerm,
    STypeAbstraction,
    STypeApplication,
    SVar,
    SRefinementApplication,
)
from aeon.sugar.program import ImportAe
from aeon.sugar.program import Program
from aeon.sugar.program import TypeDecl, InductiveDecl
from aeon.sugar.stypes import (
    SAbstractionType,
    SRefinedType,
    SRefinementPolymorphism,
    SType,
    STypeConstructor,
    STypePolymorphism,
    STypeVar,
    builtin_types,
    get_type_vars,
)
from aeon.sugar.substitutions import substitute_svartype_in_stype, substitution_svartype_in_sterm
from aeon.utils.name import Name, fresh_counter
from aeon.sugar.ast_helpers import st_int, st_string

from aeon.facade.api import ImportError


def _stype_base_int(ty: SType) -> bool:
    match ty:
        case SRefinedType(_, inner, _):
            return _stype_base_int(inner)
        case STypeConstructor(Name("Int", _), _):
            return True
        case _:
            return False


def _sugar_contains_recursive_call(t: STerm, fname: Name) -> bool:
    def is_call_tree(node: STerm) -> bool:
        cur = node
        while isinstance(cur, SApplication):
            cur = cur.fun
        return isinstance(cur, SVar) and cur == fname

    def walk(node: STerm) -> bool:
        if isinstance(node, SApplication) and is_call_tree(node):
            return True
        match node:
            case SApplication(fun, arg, _):
                return walk(fun) or walk(arg)
            case SAbstraction(_, body, _):
                return walk(body)
            case SLet(_, val, body, _):
                return walk(val) or walk(body)
            case SRec(_, _, val, body, _, _):
                return walk(val) or walk(body)
            case SIf(c, th, el, _):
                return walk(c) or walk(th) or walk(el)
            case SAnnotation(e, _, _):
                return walk(e)
            case SMatch(s, brs, _):
                return walk(s) or any(walk(b.body) for b in brs)
            case _:
                return False

    return walk(t)


def definition_with_inferred_decreasing(d: Definition) -> Definition:
    """If omitted, use the sole ``Int`` parameter as the metric for unary self-recursion."""
    if d.decreasing_by or len(d.args) != 1:
        return d
    pname, pty = d.args[0]
    if not _stype_base_int(pty):
        return d
    if not _sugar_contains_recursive_call(d.body, d.name):
        return d
    return replace(d, decreasing_by=[SVar(pname)])


class DesugaredProgram(NamedTuple):
    program: STerm
    elabcontext: ElaborationTypingContext
    metadata: Metadata


def lower_by_blocks_in_sterm(t: STerm) -> tuple[STerm, dict[Name, tuple[str, ...]]]:
    """Replace each ``SBy`` with a fresh ``SHole`` and record tactic scripts keyed by hole name."""

    def merge(a: dict[Name, tuple[str, ...]], b: dict[Name, tuple[str, ...]]) -> dict[Name, tuple[str, ...]]:
        out = dict(a)
        for k, v in b.items():
            if k in out and out[k] != v:
                raise ValueError(f"Conflicting tactic scripts for hole {k}")
            out[k] = v
        return out

    match t:
        case SBy(steps, loc=loc):
            h = Name("_by", fresh_counter.fresh())
            return SHole(h, loc=loc), {h: tuple(steps)}
        case SLiteral() | SVar() | SHole():
            return t, {}
        case SAnnotation(expr, ty, loc=loc):
            ne, s1 = lower_by_blocks_in_sterm(expr)
            return SAnnotation(ne, ty, loc=loc), s1
        case SApplication(fun, arg, loc=loc):
            nf, s1 = lower_by_blocks_in_sterm(fun)
            na, s2 = lower_by_blocks_in_sterm(arg)
            return SApplication(nf, na, loc=loc), merge(s1, s2)
        case SAbstraction(name, body, loc=loc):
            nb, s1 = lower_by_blocks_in_sterm(body)
            return SAbstraction(name, nb, loc=loc), s1
        case STypeApplication(body, ty, loc=loc):
            nb, s1 = lower_by_blocks_in_sterm(body)
            return STypeApplication(nb, ty, loc=loc), s1
        case SRefinementApplication(body, refinement, loc=loc):
            nb, s1 = lower_by_blocks_in_sterm(body)
            nr, s2 = lower_by_blocks_in_sterm(refinement)
            return SRefinementApplication(nb, nr, loc=loc), merge(s1, s2)
        case STypeAbstraction(name, kind, body, loc=loc):
            nb, s1 = lower_by_blocks_in_sterm(body)
            return STypeAbstraction(name, kind, nb, loc=loc), s1
        case SRefinementAbstraction(name, sort, body, loc=loc):
            nb, s1 = lower_by_blocks_in_sterm(body)
            return SRefinementAbstraction(name, sort, nb, loc=loc), s1
        case SIf(cond, then, otherwise, loc=loc):
            nc, s1 = lower_by_blocks_in_sterm(cond)
            nt, s2 = lower_by_blocks_in_sterm(then)
            no, s3 = lower_by_blocks_in_sterm(otherwise)
            return SIf(nc, nt, no, loc=loc), merge(merge(s1, s2), s3)
        case SMatch(scrutinee, branches, loc=loc):
            ns, s0 = lower_by_blocks_in_sterm(scrutinee)
            nbrs: list[SMatchBranch] = []
            acc = s0
            for br in branches:
                nb, sb = lower_by_blocks_in_sterm(br.body)
                acc = merge(acc, sb)
                nbrs.append(SMatchBranch(constructor=br.constructor, binders=br.binders, body=nb, loc=br.loc))
            return SMatch(ns, nbrs, loc=loc), acc
        case SLet(name, val, body, loc=loc):
            nv, s1 = lower_by_blocks_in_sterm(val)
            nb, s2 = lower_by_blocks_in_sterm(body)
            return SLet(name, nv, nb, loc=loc), merge(s1, s2)
        case SRec(name, ty, val, body, decreasing_by, loc=loc):
            nv, s1 = lower_by_blocks_in_sterm(val)
            nb, s2 = lower_by_blocks_in_sterm(body)
            decr_parts = [lower_by_blocks_in_sterm(m) for m in decreasing_by]
            nd = tuple(p[0] for p in decr_parts)
            s_decr: dict[Name, tuple[str, ...]] = {}
            for _, sd in decr_parts:
                s_decr = merge(s_decr, sd)
            return SRec(name, ty, nv, nb, decreasing_by=nd, loc=loc), merge(merge(s1, s2), s_decr)
        case _:
            assert False, f"lower_by_blocks_in_sterm: unhandled {t} ({type(t)})"


def lower_by_blocks_in_definitions(
    definitions: list[Definition], metadata: Metadata
) -> tuple[list[Definition], Metadata]:
    new_definitions: list[Definition] = []
    for d in definitions:
        match d:
            case Definition(name, foralls, args, rtype, body, decorators, rforalls, decreasing_by, loc):
                nbody, scripts = lower_by_blocks_in_sterm(body)
                if scripts:
                    cur = dict(metadata.get(name, {}))
                    ts = dict(cur.get("tactic_scripts", {}))
                    for h, steps in scripts.items():
                        if h in ts and ts[h] != steps:
                            raise ValueError(f"Multiple conflicting `by` scripts for {name} hole {h}")
                        ts[h] = steps
                    cur["tactic_scripts"] = ts
                    metadata[name] = cur
                new_definitions.append(
                    Definition(
                        name,
                        foralls,
                        args,
                        rtype,
                        nbody,
                        decorators,
                        rforalls,
                        decreasing_by,
                        loc,
                    )
                )
            case _:
                assert False, f"lower_by_blocks_in_definitions: {d}"
    return new_definitions, metadata


def desugar(p: Program, is_main_hole: bool = True, extra_vars: dict[Name, SType] | None = None) -> DesugaredProgram:
    vs: dict[Name, SType] = {} if extra_vars is None else extra_vars
    vs.update(typing_vars)

    # We need inductive constructor info to lower `match` expressions.
    # Note: `expand_inductive_decls` clears `p.inductive_decls`, so we snapshot it here.
    inductive_decls_snapshot = list(p.inductive_decls)

    p = expand_inductive_decls(p)

    prog = determine_main_function(p, is_main_hole)

    defs, type_decls = p.definitions, p.type_decls
    defs, type_decls = handle_imports(p.imports, defs, type_decls)

    defs, metadata = apply_decorators_in_definitions(defs)
    defs, metadata = lower_by_blocks_in_definitions(defs, metadata)

    defs = introduce_forall_in_types(defs, type_decls)
    defs = introduce_rforall_in_types(defs)

    etctx = build_typing_context(vs, type_decls)
    etctx, prog = update_program_and_context(prog, defs, etctx)
    prog, etctx = replace_concrete_types(
        prog, etctx, [Name(t, 0) for t in builtin_types] + [td.name for td in type_decls]
    )
    # Lower match expressions (Lean syntax) into the generated inductive eliminators.
    prog = lower_match_to_inductive_rec(prog, inductive_decls_snapshot)
    return DesugaredProgram(prog, etctx, metadata)


def lower_match_to_inductive_rec(prog: STerm, inductive_decls: list[InductiveDecl]) -> STerm:
    """
    Rewrite `match scrutinee with | C x y => e | ...` into:
        <Inductive>_rec scrutinee (\\x -> \\y -> e) ...
    using the generated `<Inductive>_rec` eliminator introduced by `expand_inductive_decls`.
    """

    # Build quick lookup: (inductive_name, constructor_name) -> constructor argument binders.
    inductive_info: dict[Name, dict[Name, list[tuple[Name, SType]]]] = {}
    for decl in inductive_decls:
        cons_map: dict[Name, list[tuple[Name, SType]]] = {}
        for cons in decl.constructors:
            # Each constructor is represented as a Definition in sugar, where `args`
            # already carries the types we need to place the bound variables.
            match cons:
                case Definition(cname, _, cargs, _, _, _, _, _, _):
                    cons_map[cname] = cargs
        inductive_info[decl.name] = cons_map

    def lower_term(t: STerm) -> STerm:
        match t:
            case SMatch(scrutinee, branches, loc=_):
                lowered_scrut = lower_term(scrutinee)

                # Determine which inductive we're matching on from the constructor list.
                # We only support matching on values of an inductive type whose name can
                # be inferred from the branch constructor names.
                lowered_branches: list[SMatchBranch] = branches
                cons_names = [b.constructor for b in lowered_branches]

                # Find the first inductive that contains all branch constructors.
                chosen: Name | None = None
                chosen_cons_map: dict[Name, list[tuple[Name, SType]]] | None = None
                for iname, cmap in inductive_info.items():
                    if all(cn in cmap for cn in cons_names):
                        chosen = iname
                        chosen_cons_map = cmap
                        break

                if chosen is None or chosen_cons_map is None:
                    # Fall back: this should typically be rejected by typechecking later.
                    return SMatch(lowered_scrut, lowered_branches, loc=t.loc)

                rec_name = Name(chosen.name + "_rec", -1)
                rec_fun: STerm = SVar(rec_name, loc=t.loc)  # will be bound like any other var

                # Constructor handlers must be passed to the eliminator in constructor order,
                # so gather them in the same order as the inductive declaration.
                handlers: list[STerm] = []
                for decl in inductive_decls:
                    if decl.name != chosen:
                        continue
                    for cons_def in decl.constructors:
                        match cons_def:
                            case Definition(cname, _, cargs, _, _, _, _, _, _):
                                # Find the matching branch, if missing use a hole-like undefined.
                                branch_expr = None
                                for b in lowered_branches:
                                    if b.constructor == cname:
                                        branch_expr = b.body
                                        branch_binders = b.binders
                                        break
                                if branch_expr is None:
                                    branch_expr = SHole(Name("todo", -1), loc=t.loc)
                                    branch_binders = [arg for arg, _ in cargs]

                                # Prefer binders from the pattern; if empty, use constructor arg names.
                                binders = branch_binders if branch_binders else [arg for (arg, _) in cargs]

                                body: STerm = lower_term(branch_expr)
                                # Build nested abstractions for each binder.
                                for bn in reversed(binders):
                                    body = SAbstraction(bn, body, loc=t.loc)
                                handlers.append(body)

                # Apply: ((rec_fun scrut) handler1) handler2 ...
                out: STerm = SApplication(rec_fun, lowered_scrut, loc=t.loc)
                for h in handlers:
                    out = SApplication(out, h, loc=t.loc)
                return out

            case SApplication(fun, arg, loc=loc):
                return SApplication(lower_term(fun), lower_term(arg), loc=loc)
            case SAbstraction(name, body, loc=loc):
                return SAbstraction(name, lower_term(body), loc=loc)
            case SLet(name, val, body, loc=loc):
                return SLet(name, lower_term(val), lower_term(body), loc=loc)
            case SRec(name, ty, val, body, decreasing_by, loc=loc):
                nd = tuple(lower_term(m) for m in decreasing_by)
                return SRec(name, ty, lower_term(val), lower_term(body), decreasing_by=nd, loc=loc)
            case SIf(cond, then, otherwise, loc=loc):
                return SIf(lower_term(cond), lower_term(then), lower_term(otherwise), loc=loc)
            case SAnnotation(expr, ty, loc=loc):
                return SAnnotation(lower_term(expr), ty, loc=loc)
            case STypeApplication(body, ty, loc=loc):
                return STypeApplication(lower_term(body), ty, loc=loc)
            case STypeAbstraction(name, kind, body, loc=loc):
                return STypeAbstraction(name, kind, lower_term(body), loc=loc)
            case SRefinementApplication(body, refinement, loc=loc):
                return SRefinementApplication(lower_term(body), lower_term(refinement), loc=loc)
            case SRefinementAbstraction(pname, sort, body, loc=loc):
                return SRefinementAbstraction(pname, sort, lower_term(body), loc=loc)
            case _:
                return t

    return lower_term(prog)


def expand_inductive_decls(p: Program) -> Program:
    tds: list[TypeDecl] = []
    defs: list[Definition] = []

    uninterpreted_lit = SVar(Name("uninterpreted", 0))

    for decl in p.inductive_decls:
        match decl:
            case InductiveDecl(name, args, constructors, measures, loc):
                tds.append(TypeDecl(name, args))

                for measure in measures:
                    match measure:
                        case Definition(mname, mforalls, margs, mrtype, _, _, _, _, mloc):
                            de = Definition(mname, mforalls, margs, mrtype, uninterpreted_lit, loc=mloc)
                            defs.append(de)

                def key_for(tyname: Name, constructor_name: Name) -> str:
                    return f"{tyname.name}_{constructor_name.name}"

                for constructor in constructors:
                    match constructor:
                        case Definition(cname, cforalls, cargs, crtype, _, _, _, _, cloc):
                            arg_s = ", ".join(str(arg.name) for (arg, _) in cargs)
                            mk_tuple = SApplication(
                                SVar(Name("native", 0)), SLiteral(f"('{key_for(name, cname)}', {arg_s})", st_string)
                            )
                            de = Definition(cname, cforalls, cargs, crtype, mk_tuple, loc=cloc)
                            defs.append(de)

                def curry(args: list[tuple[Name, SType]], rty: SType) -> SType:
                    for aname, aty in args[::-1]:
                        rty = SAbstractionType(aname, aty, rty)
                    return rty

                def case_for(cname: Name, cargs: list[tuple[Name, SType]]) -> str:
                    pargs = ", ".join(f"{arg.name}" for (arg, _) in cargs)
                    args = "".join(f"({arg.name})" for (arg, _) in cargs)
                    return f"\tcase ('{key_for(name, cname)}', {pargs}):\n\t\treturn case_{cname.name}{args}"

                cases = "\n".join(case_for(cons.name, cons.args) for cons in constructors)
                catchall = "\n\tcase _:\n\t\traise Exception('Invalid constructor')"
                rec_body: STerm = SApplication(
                    SVar(Name("native", 0)), SLiteral(f"""match this:\n{cases}{catchall}\n""", st_string)
                )

                foralls: list[tuple[Name, Kind]] = []
                rec_args: list[tuple[Name, SType]] = []

                # Return Type
                return_generic_name = Name("ret", -1)
                return_type = STypeVar(return_generic_name)
                foralls.append((return_generic_name, BaseKind()))

                # Target Type (First argument)
                # foralls.extend([ (arg, BaseKind()) for arg in args ])
                target_type = STypeConstructor(name, [STypeVar(a) for a in args])
                rec_args.append((Name("this", -1), target_type))

                # Prepare arguments for each constructor
                for cons in constructors:
                    rec_args.append((Name(f"case_{cons.name.name}", -1), curry(cons.args, return_type)))

                rec_de = Definition(
                    name=Name(name.name + "_rec", -1),
                    foralls=foralls,
                    args=rec_args,
                    type=return_type,
                    body=rec_body,
                    rforalls=[],
                    decreasing_by=[],
                    loc=loc,
                )
                defs.append(rec_de)

            case _:
                assert False, f"Unexpected inductive decl {decl} in {p}"

    return Program(p.imports, p.type_decls + tds, [], defs + p.definitions)


def introduce_forall_in_types(defs: list[Definition], type_decls: list[TypeDecl]) -> list[Definition]:
    types = [td.name for td in type_decls]
    ndefs = []
    for d in defs:
        match d:
            case Definition(name, foralls, args, rtype, body, decorators, rforalls, decreasing_by, loc):
                new_foralls: list[tuple[Name, Kind]] = []

                tlst: list[SType] = [ty for _, ty in args] + [rtype]
                for ty in tlst:
                    for t in get_type_vars(ty):
                        tname = t.name
                        if tname not in types:
                            entry = (tname, BaseKind())
                            if entry not in new_foralls:
                                new_foralls.append(entry)
                ndefs.append(
                    Definition(
                        name,
                        foralls + new_foralls,
                        args,
                        rtype,
                        body,
                        decorators,
                        rforalls,
                        decreasing_by,
                        loc,
                    )
                )
    return ndefs


def _collect_implicit_refinement_params(ty: SType, bound_rho: set[Name], acc: dict[Name, SType]) -> None:
    def rec(t: SType, rho: set[Name]) -> None:
        _collect_implicit_refinement_params(t, rho, acc)

    match ty:
        case SRefinementPolymorphism(rname, sort, body):
            rec(sort, bound_rho)
            rec(body, bound_rho | {rname})
        case STypePolymorphism(_, _, body):
            rec(body, bound_rho)
        case SAbstractionType(_, vt, rt):
            rec(vt, bound_rho)
            rec(rt, bound_rho)
        case SRefinedType(binder, base, ref):
            rec(base, bound_rho)
            match ref:
                case SApplication(SVar(p), SVar(b)) if b == binder and p not in bound_rho:
                    if p in acc:
                        if acc[p] != base:
                            raise TypeError(
                                f"Inconsistent sorts for implicit refinement parameter {p.name}: {acc[p]} vs {base}"
                            )
                    else:
                        acc[p] = base
                case _:
                    pass
        case STypeConstructor(_, ty_args):
            for a in ty_args:
                rec(a, bound_rho)
        case STypeVar(_):
            pass
        case _:
            assert False, f"_collect_implicit_refinement_params: unhandled {ty} ({type(ty)})"


def introduce_rforall_in_types(defs: list[Definition]) -> list[Definition]:
    """Discover implicit `p` from `t<p>`, append to `rforalls` (with parser `p`s).

    If `rtype` begins with `forall t` and there are any `p`s, splice those `∀p`
    into the body of that `∀t` and clear `rforalls` so later passes do not wrap
    `∀p` around the whole type (which would put `p` outside `t` and break `f[t]`).
    Otherwise keep the merged `rforalls` list for `convert_definition_to_srec`.
    """
    ndefs: list[Definition] = []
    for d in defs:
        match d:
            case Definition(name, foralls, args, rtype, body, decorators, rforalls, decreasing_by, loc):
                acc: dict[Name, SType] = {}
                tlst: list[SType] = [ty for _, ty in args] + [rtype]
                for ty in tlst:
                    _collect_implicit_refinement_params(ty, set(), acc)
                existing = {p for p, _ in rforalls}
                new_entries = [(p, s) for p, s in acc.items() if p not in existing]
                merged_rforalls = rforalls + new_entries

                final_rtype = rtype
                final_rforalls = merged_rforalls
                if merged_rforalls:
                    match rtype:
                        case STypePolymorphism(tn, tk, tbody):
                            inner = tbody
                            for pname, psort in merged_rforalls:
                                inner = SRefinementPolymorphism(pname, psort, inner, loc=loc)
                            final_rtype = STypePolymorphism(tn, tk, inner, loc=rtype.loc)
                            final_rforalls = []
                        case _:
                            pass

                ndefs.append(
                    Definition(
                        name,
                        foralls,
                        args,
                        final_rtype,
                        body,
                        decorators,
                        final_rforalls,
                        decreasing_by,
                        loc,
                    )
                )
    return ndefs


def determine_main_function(p: Program, is_main_hole: bool = True) -> STerm:
    for d in p.definitions:
        match d.name:
            case Name("main", id):
                return SApplication(SVar(Name("main", id)), SLiteral(1, type=st_int))
    if is_main_hole:
        return SHole(Name("main", 0))
    else:
        return SLiteral(1, st_int)


def handle_imports(
    imports: list[ImportAe],
    defs: list[Definition],
    type_decls: list[TypeDecl],
) -> tuple[list[Definition], list[TypeDecl]]:
    for imp in imports[::-1]:
        import_p = handle_import(imp)
        import_p_definitions = import_p.definitions
        defs_recursive: list[Definition] = []
        type_decls_recursive: list[TypeDecl] = []
        if import_p.imports:
            defs_recursive, type_decls_recursive = handle_imports(
                import_p.imports,
                import_p.definitions,
                import_p.type_decls,
            )
        if imp.func:
            import_p_definitions = [d for d in import_p_definitions if str(d.name.name) == imp.func]

        defs = defs_recursive + import_p_definitions + defs
        type_decls = type_decls_recursive + import_p.type_decls + type_decls
    return defs, type_decls


def apply_decorators_in_program(prog: Program) -> Program:
    """We apply the decorators meta-programming code to each definition in the
    program."""
    defs, _ = apply_decorators_in_definitions(prog.definitions)
    return Program(
        imports=prog.imports,
        type_decls=prog.type_decls,
        inductive_decls=prog.inductive_decls,
        definitions=defs,
    )


def apply_decorators_in_definitions(definitions: list[Definition]) -> tuple[list[Definition], Metadata]:
    """We apply the decorators meta-programming code to each definition in the
    program."""
    metadata: Metadata = {}
    new_definitions = []
    for definition in definitions:
        new_def, other_defs, metadata = apply_decorators(definition, metadata)
        new_definitions.append(new_def)
        new_definitions.extend(other_defs)
    return new_definitions, metadata


def update_program_and_context(
    prog: STerm,
    defs: list[Definition],
    ctx: ElaborationTypingContext,
) -> tuple[ElaborationTypingContext, STerm]:
    for d in defs[::-1]:
        match d.body:
            case SVar(Name("uninterpreted", _)):
                ctx.entries.append(ElabUninterpretedBinder(d.name, type_of_definition(d)))
            case _:
                prog = convert_definition_to_srec(prog, d)
    return ctx, prog


def replace_concrete_types(
    t: STerm, etctx: ElaborationTypingContext, types: list[Name]
) -> tuple[STerm, ElaborationTypingContext]:
    """Replaces all occurrences of STypeVar with the corresponding STypeConstructor."""
    for name in types:
        t = substitution_svartype_in_sterm(t, STypeConstructor(name), name)

    def fix_vartype(e: ElabTypingContextEntry) -> ElabTypingContextEntry:
        match e:
            case ElabVariableBinder(vname, ty):
                nty = ty
                for name in types:
                    nty = substitute_svartype_in_stype(nty, STypeConstructor(name), name)
                return ElabVariableBinder(vname, nty)
            case ElabUninterpretedBinder(vname, ty):
                nty = ty
                for name in types:
                    nty = substitute_svartype_in_stype(nty, STypeConstructor(name), name)
                return ElabUninterpretedBinder(vname, nty)
            case _:
                return e

    return t, ElaborationTypingContext([fix_vartype(e) for e in etctx.entries])


def type_of_definition(d: Definition) -> SType:
    match d:
        case Definition(_, foralls, args, rtype, _, _, rforalls, _, loc):
            ntype = rtype
            for name, atype in reversed(args):
                ntype = SAbstractionType(name, atype, ntype, loc)
            for name, sort in reversed(rforalls):
                ntype = SRefinementPolymorphism(name, sort, ntype, loc)
            for name, kind in reversed(foralls):
                ntype = STypePolymorphism(name, kind, ntype, loc)
            return ntype
        case _:
            assert False, f"{d} is not a definition"


def convert_definition_to_srec(prog: STerm, d: Definition) -> STerm:
    d = definition_with_inferred_decreasing(d)
    match d:
        case Definition(dname, foralls, args, rtype, body, _, rforalls, decreasing_by, loc):
            ntype = rtype
            nbody = body
            for name, atype in reversed(args):
                ntype = SAbstractionType(name, atype, ntype, loc=loc)
                nbody = SAbstraction(name, nbody, loc=loc)
            for name, sort in reversed(rforalls):
                ntype = SRefinementPolymorphism(name, sort, ntype, loc=loc)
                nbody = SRefinementAbstraction(name, sort, nbody, loc=loc)
            for name, kind in reversed(foralls):
                ntype = STypePolymorphism(name, kind, ntype, loc=loc)
                nbody = STypeAbstraction(name, kind, nbody, loc=loc)
            return SRec(dname, ntype, nbody, prog, decreasing_by=tuple(decreasing_by), loc=loc)
        case _:
            assert False, f"{d} is not a definition"


def handle_import(imp: ImportAe) -> Program:
    """Imports a given path, following the precedence rules of current folder,
    AEONPATH."""
    path = imp.path
    possible_containers = (
        [Path.cwd()] + [Path.cwd() / "libraries"] + [Path(s) for s in os.environ.get("AEONPATH", ";").split(";") if s]
    )
    for container in possible_containers:
        file = container / f"{path}"
        if file.exists():
            contents = open(file).read()
            parse = mk_parser("program", filename=str(file))
            return parse(contents)
    raise ImportError(importel=imp, possible_containers=possible_containers)
