from __future__ import annotations

import os
from pathlib import Path
from typing import NamedTuple
from loguru import logger

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
    SHole,
    SLiteral,
    SRec,
    STerm,
    STypeAbstraction,
    SVar,
)
from aeon.sugar.program import ImportAe
from aeon.sugar.program import Program
from aeon.sugar.program import TypeDecl, InductiveDecl
from aeon.sugar.stypes import (
    SAbstractionType,
    SType,
    STypePolymorphism,
    SRefinementPolymorphism,
    builtin_types,
    get_type_vars,
    STypeConstructor,
    SRefinedType,
)
from aeon.sugar.substitutions import substitute_svartype_in_stype, substitution_svartype_in_sterm
from aeon.utils.name import Name, fresh_counter
from aeon.sugar.ast_helpers import st_int, st_string

from aeon.sugar.stypes import STypeVar
from aeon.facade.api import ImportError


class DesugaredProgram(NamedTuple):
    program: STerm
    elabcontext: ElaborationTypingContext
    metadata: Metadata

    def __str__(self):
        return f"DesugaredProgram(\nprogram={self.program}, \nelabcontext={self.elabcontext} metadata={self.metadata})"


def desugar(p: Program, is_main_hole: bool = True, extra_vars: dict[Name, SType] | None = None) -> DesugaredProgram:
    vs: dict[Name, SType] = {} if extra_vars is None else extra_vars
    vs.update(typing_vars)

    p = expand_inductive_decls(p)

    prog = determine_main_function(p, is_main_hole)

    defs, type_decls = p.definitions, p.type_decls
    defs, type_decls = handle_imports(p.imports, defs, type_decls)

    defs, metadata = apply_decorators_in_definitions(defs)

    defs = introduce_forall_in_types(defs, type_decls)

    etctx = build_typing_context(vs, type_decls)

    defs = introduce_forall_in_refinements(defs, etctx)
    # logger.log("AST_INFO", f"Definitions after introducing foralls: {defs}")

    etctx, prog = update_program_and_context(prog, defs, etctx)
    # logger.log("AST_INFO", f"Program after updating context: {prog}")
    prog, etctx = replace_concrete_types(
        prog, etctx, [Name(t, 0) for t in builtin_types] + [td.name for td in type_decls]
    )
    # logger.log("AST_INFO", f"Program after replacing concrete types: {prog}")
    return DesugaredProgram(prog, etctx, metadata)


def expand_inductive_decls(p: Program) -> Program:
    tds: list[TypeDecl] = []
    defs: list[Definition] = []

    uninterpreted_lit = SVar(Name("uninterpreted", 0))

    for decl in p.inductive_decls:
        match decl:
            case InductiveDecl(name, args, constructors, measures):
                tds.append(TypeDecl(name, args))

                for measure in measures:
                    match measure:
                        case Definition(mname, mforalls, mrforalls, margs, mrtype, _, _):
                            de = Definition(mname, mforalls, mrforalls, margs, mrtype, uninterpreted_lit)
                            defs.append(de)

                def key_for(tyname: Name, constructor_name: Name) -> str:
                    return f"{tyname.name}_{constructor_name.name}"

                for constructor in constructors:
                    match constructor:
                        case Definition(cname, cforalls, crforalls, cargs, crtype, _, _):
                            arg_s = ", ".join(str(arg.name) for (arg, _) in cargs)
                            mk_tuple = SApplication(
                                SVar(Name("native", 0)), SLiteral(f"('{key_for(name, cname)}', {arg_s})", st_string)
                            )
                            de = Definition(cname, cforalls, crforalls, cargs, crtype, mk_tuple)
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
                rforalls: list[tuple[Name, SType]] = []
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
                    rforalls=rforalls,
                    args=rec_args,
                    type=return_type,
                    body=rec_body,
                )
                defs.append(rec_de)

            case _:
                assert False, f"Unexpected inductive decl {decl} in {p}"

    return Program(p.imports, p.type_decls + tds, [], defs + p.definitions)


def introduce_forall_in_types(defs: list[Definition], type_decls: list[TypeDecl]) -> list[Definition]:
    # logger.log("AST_INFO", "Introducing forall in types")
    types = [td.name for td in type_decls]
    # logger.log("AST_INFO", f"Types in program: {types}")
    ndefs = []
    for d in defs:
        match d:
            case Definition(name, foralls, rforalls, args, rtype, body, decorators):
                # logger.log("AST_INFO", f"Processing definition {name} with args {[f"{name} : {_type}" for name, _type in args]} and type {rtype}")

                new_foralls: list[tuple[Name, Kind]] = []

                tlst: list[SType] = [ty for _, ty in args] + [rtype]
                for ty in tlst:
                    # logger.log("AST_INFO", f"Processing type {ty}")
                    for t in get_type_vars(ty):
                        tname = t.name
                        # logger.log("AST_INFO", f"Processing type variable {tname}")
                        if tname not in types:
                            # logger.log("AST_INFO", f"Adding type variable {tname} to foralls")
                            entry = (tname, BaseKind())
                            if entry not in new_foralls:
                                # logger.log("AST_INFO", f"Added {entry} to foralls")
                                new_foralls.append(entry)
                # logger.log("AST_INFO", f"New foralls: {new_foralls}")
                ndefs.append(Definition(name, foralls + new_foralls, rforalls, args, rtype, body, decorators))
    # for td in ndefs:
    # logger.log("AST_INFO", f"New definition: {td}")
    return ndefs


def introduce_forall_in_refinements(defs: list[Definition], type_decls: ElaborationTypingContext) -> list[Definition]:
    # logger.log("AST_INFO", "Introducing forall in refinements")
    ndefs = []
    for d in defs:
        match d:
            case Definition(name, foralls, rforalls, args, rtype, body, decorators):
                # logger.log("AST_INFO", f"Processing definition {name} with args {[f'{name} : {_type}' for name, _type in args]} and type {rtype}")

                new_foralls: list[tuple[Name, SType]] = []
                rlst: list[SType] = [ty for _, ty in args] + [rtype]
                for ty in rlst:
                    # logger.log("AST_INFO", f"Processing refinement type {ty}")
                    match ty:
                        case SRefinedType(rname, reftype, ref):
                            logger.log("AST_INFO", f"Processing refinement {rname} in {ty} with ref {ref}")
                            curr = ref
                            argtype: SType = STypeConstructor(Name("Bool", 0))
                            while isinstance(curr, SApplication):
                                match curr:
                                    case SApplication(a, b):
                                        logger.log(
                                            "AST_INFO", f"Refinement is an application {a}|{type(a)} {b}|{type(b)}"
                                        )
                                        match b:
                                            case SVar(vname):
                                                if vname.name == rname.name:
                                                    argtype = SAbstractionType(
                                                        Name(vname.name, fresh_counter.fresh()), reftype, argtype
                                                    )
                                                else:
                                                    argtype = SAbstractionType(
                                                        Name(vname.name, fresh_counter.fresh()),
                                                        STypeVar(vname),
                                                        argtype,
                                                    )
                                            case SLiteral(_, ntype):
                                                argtype = SAbstractionType(
                                                    Name("arg", fresh_counter.fresh()), ntype, argtype
                                                )
                                        curr = a
                                    case _:
                                        assert False, f"Unexpected refinement type {curr} in {ty}"
                            logger.log("AST_INFO", f"Refinement parameter {curr}|{type(curr)} with arg type {argtype}")
                            match curr:
                                case SVar(vname):
                                    if not any(vname.name == rname.name for rname, _ in new_foralls):
                                        new_foralls.append((vname, argtype))
                logger.log("AST_INFO", f"New foralls: {new_foralls}")
                ndefs.append(Definition(name, foralls, rforalls + new_foralls, args, rtype, body, decorators))
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
        case Definition(_, foralls, rforalls, args, rtype, _, _):
            ntype = rtype
            for name, atype in reversed(args):
                ntype = SAbstractionType(name, atype, ntype)
            for name, kind in reversed(foralls):
                ntype = STypePolymorphism(name, kind, ntype)
            for name, type in reversed(rforalls):
                ntype = SRefinementPolymorphism(name, type, ntype)
            return ntype
        case _:
            assert False, f"{d} is not a definition"


def convert_definition_to_srec(prog: STerm, d: Definition) -> STerm:
    # logger.log("AST_INFO", f"Converting definition {d.name} to SRec")
    match d:
        case Definition(dname, foralls, rforalls, args, rtype, body, _):
            # logger.log("AST_INFO", f"Processing definition {dname} with args {[f'{name} : {_type}' for name, _type in args]} and type {rtype}")
            ntype = rtype
            nbody = body
            for name, atype in reversed(args):
                ntype = SAbstractionType(name, atype, ntype)
                nbody = SAbstraction(name, nbody)
            for name, kind in reversed(foralls):
                ntype = STypePolymorphism(name, kind, ntype)
                nbody = STypeAbstraction(name, kind, nbody)
            # logger.log("AST_INFO", f"Refinement foralls: {rforalls}")
            for name, type in reversed(rforalls):
                ntype = SRefinementPolymorphism(name, type, ntype)
                # nbody = SRefinementAbstraction(name, kind, nbody)
            # logger.log("AST_INFO", f"Converted definition {dname} to SRec with type {ntype} and body {nbody}")
            return SRec(dname, ntype, nbody, prog)
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
            parse = mk_parser("program")
            return parse(contents)
    raise ImportError(importel=imp, possible_containers=possible_containers)
