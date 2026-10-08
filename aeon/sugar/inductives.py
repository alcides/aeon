"""Inductive declaration expansion and rforall inference for desugaring."""

from __future__ import annotations

from dataclasses import replace

from aeon.core.multiplicity import MOmega, Multiplicity
from aeon.core.types import Kind
from aeon.sugar.ast_helpers import st_bool, st_string
from aeon.sugar.program import (
    Definition,
    InductiveDecl,
    Program,
    SApplication,
    SLiteral,
    STerm,
    SVar,
    TypeDecl,
)
from aeon.sugar.equality import type_equality
from aeon.sugar.substitutions import substitution_sterm_in_stype
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


def _merge_inductive_rforalls(
    dtype_rfs: list[tuple[Name, SType]], local_rfs: list[tuple[Name, SType]]
) -> list[tuple[Name, SType]]:
    """Datatype-level abstract refinements (Liquid Haskell ``data T <p>``) scope over every constructor."""
    seen = {n for n, _ in dtype_rfs}
    return list(dtype_rfs) + [(n, t) for n, t in local_rfs if n not in seen]


def canonical_measure_name(inductive: Name, measure: Name) -> Name:
    """Return the unique compiler name for a measure declared by an inductive.

    Surface declarations use a short name (usually ``size``), but that name is
    scoped by the inductive declaration.  The rest of the compiler and SMT
    backend must never see that short alias: ``List.size`` is always represented
    as ``List_size``.
    """
    return Name(f"{inductive.name}_{measure.name}", measure.id)


def _canonicalize_measure_references(ty: SType, inductive: Name, measures: list[Definition]) -> SType:
    """Qualify this inductive's unbound measure references in a type.

    Constructor signatures are expanded before general name resolution.  Their
    measure uses are therefore still unbound ``size?`` variables; resolving a
    shared short name later would associate two ``+ size`` declarations with
    whichever happened to be visited last.  Rewrite them while the owning
    inductive is known.
    """
    result = ty
    for measure in measures:
        canonical = canonical_measure_name(inductive, measure.name)
        result = substitution_sterm_in_stype(result, SVar(canonical), measure.name)
    return result


def _eligible_refinement_base_for_inductive(ind: InductiveDecl, base: SType) -> bool:
    """True when an abstract refinement predicate ranges over this datatype or one of its parameters."""
    match base:
        case STypeConstructor(n, _):
            return n == ind.name or n.name == ind.name.name
        case STypeVar(tv):
            return any(tv.name == a.name for a in ind.args) or tv.name == ind.name.name
        case SRefinedType(_, inner, _):
            return _eligible_refinement_base_for_inductive(ind, inner)
        case _:
            return False


def _is_implicit_refinement_param(p: Name, bound_rho: set[Name]) -> bool:
    """Whether a predicate name ``p`` in a refinement ``{v | p v}`` should be
    treated as an *implicit* (abstract) refinement parameter to be universally
    generalised, rather than a reference to a defined function.

    An implicit refinement parameter is an *unbound* predicate variable
    (``Name.id == -1``): binding leaves it unresolved because it has no binder.
    A predicate that resolves to a real symbol — a top-level ``def`` (e.g. an
    ``uninterpreted`` predicate like ``admin``), a builtin, or an import — is
    bound to a concrete ``id`` and must be kept as an ordinary application so
    its refinement stays a checked obligation (issue #468). Explicitly-bound
    ``forall <p>`` parameters live in ``bound_rho`` and are also excluded.
    """
    return p.id == -1 and p not in bound_rho


def _collect_implicit_refinement_params_for_inductive(
    ind: InductiveDecl, ty: SType, bound_rho: set[Name], acc: dict[Name, SType]
) -> None:
    """Like ``_collect_implicit_refinement_params``, but only records predicates over ``ind`` or its type params."""

    def rec(t: SType, rho: set[Name]) -> None:
        _collect_implicit_refinement_params_for_inductive(ind, t, rho, acc)

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
                case SApplication(SVar(p), SVar(b)) if b == binder and _is_implicit_refinement_param(p, bound_rho):
                    # The inferred sort is the full predicate type ``base -> Bool``.
                    pred_ty = SAbstractionType(Name("_"), base, st_bool)
                    if not _eligible_refinement_base_for_inductive(ind, base):
                        pass
                    elif p in acc:
                        if not type_equality(acc[p], pred_ty):
                            raise TypeError(
                                f"Inconsistent sorts for inferred datatype refinement {p.name} "
                                f"on {ind.name.name}: {acc[p]} vs {pred_ty}"
                            )
                    else:
                        acc[p] = pred_ty
                case _:
                    pass
        case STypeConstructor(_, ty_args):
            for a in ty_args:
                rec(a, bound_rho)
        case STypeVar(_):
            pass
        case _:
            assert False, f"_collect_implicit_refinement_params_for_inductive: unhandled {ty} ({type(ty)})"


def infer_inductive_rforall_decls(p: Program) -> Program:
    """If an inductive omits ``forall <p : …>``, infer datatype ``rforalls`` from refinements in constructor and
    measure signatures, and from the types of top-level definitions (Liquid Haskell-style abstract refinements).
    """
    inferred: list[InductiveDecl] = []
    for ind in p.inductive_decls:
        if ind.rforalls:
            inferred.append(ind)
            continue
        acc: dict[Name, SType] = {}

        def scan(ty: SType) -> None:
            _collect_implicit_refinement_params_for_inductive(ind, ty, set(), acc)

        for cons in ind.constructors:
            match cons:
                case Definition(_, _, cargs, crtype, _, _, _, _, _):
                    for _, at in cargs:
                        scan(at)
                    scan(crtype)
        for meas in ind.measures:
            match meas:
                case Definition(_, _, margs, mrtype, _, _, _, _, _):
                    for _, at in margs:
                        scan(at)
                    scan(mrtype)
        for d in p.definitions:
            match d:
                case Definition(_, _, dargs, drtype, _, _, _, _, _):
                    for _, at in dargs:
                        scan(at)
                    scan(drtype)

        if acc:
            ordered = sorted(acc.items(), key=lambda item: (item[0].name, item[0].id))
            inferred.append(replace(ind, rforalls=list(ordered)))
        else:
            inferred.append(ind)

    return Program(
        p.imports,
        p.type_decls,
        inferred,
        p.definitions,
        p.class_decls,
        p.instance_decls,
        p.export_names,
        p.reexports,
    )


def expand_inductive_decls(p: Program) -> Program:
    tds: list[TypeDecl] = []
    defs: list[Definition] = []

    uninterpreted_lit = SVar(Name("uninterpreted", 0))

    for decl in p.inductive_decls:
        match decl:
            case InductiveDecl(name, args, dtype_rfs, constructors, measures, loc):
                tds.append(TypeDecl(name, args, list(dtype_rfs)))

                for measure in measures:
                    match measure:
                        case Definition(mname, mforalls, margs, mrtype, _, mdecs, m_rf, m_decr, mloc):
                            merged_m_rf = _merge_inductive_rforalls(dtype_rfs, m_rf)
                            de = Definition(
                                canonical_measure_name(name, mname),
                                mforalls,
                                [
                                    (arg_name, _canonicalize_measure_references(arg_ty, name, measures))
                                    for arg_name, arg_ty in margs
                                ],
                                _canonicalize_measure_references(mrtype, name, measures),
                                uninterpreted_lit,
                                mdecs,
                                merged_m_rf,
                                m_decr,
                                loc=mloc,
                            )
                            defs.append(de)

                def key_for(tyname: Name, constructor_name: Name) -> str:
                    return f"{tyname.name}_{constructor_name.name}"

                def field_skeleton(ty: SType, type_params: list[Name], self_name: str) -> str:
                    match ty:
                        case SRefinedType(_, inner, _):
                            return field_skeleton(inner, type_params, self_name)
                        case STypeVar(n):
                            if n.name == self_name:
                                return self_name
                            for i, tp in enumerate(type_params):
                                if tp.name == n.name:
                                    return f"#{i}"
                            # Unresolved name used as a type var — often another
                            # inductive in the same program; treat as ADT.
                            return n.name
                        case STypeConstructor(n, _):
                            return n.name
                        case _:
                            return "Int"

                # Register constructor groups for SMT distinctness assertions
                # and LH-style measures (``+ size`` → recursive Z3 definitions).
                from aeon.verification.constructor_registry import register_constructors, register_measures

                field_types: dict[str, list[str]] = {}
                for constructor in constructors:
                    match constructor:
                        case Definition(cname, _, cargs, _, _, _, _, _, _):
                            field_types[key_for(name, cname)] = [
                                field_skeleton(ty, args, name.name) for (_, ty) in cargs
                            ]

                register_constructors(
                    name.name,
                    [key_for(name, cons.name) for cons in constructors],
                    type_param_count=len(args),
                    field_types=field_types,
                )
                canonical_measures = [canonical_measure_name(name, measure.name).name for measure in measures]
                if canonical_measures:
                    register_measures(name.name, canonical_measures)
                for constructor in constructors:
                    match constructor:
                        case Definition(cname, cforalls, cargs, crtype, _, cdecs, c_rf, c_decr, cloc):
                            arg_s = ", ".join(str(arg.name) for (arg, _) in cargs)
                            mk_tuple = SApplication(
                                SVar(Name("native", 0)), SLiteral(f"('{key_for(name, cname)}', {arg_s})", st_string)
                            )
                            merged_c_rf = _merge_inductive_rforalls(dtype_rfs, c_rf)
                            # Prefix constructor name with type name to namespace it
                            prefixed_cname = Name(f"{name.name}_{cname.name}", cname.id)
                            de = Definition(
                                prefixed_cname,
                                cforalls,
                                [
                                    (arg_name, _canonicalize_measure_references(arg_ty, name, measures))
                                    for arg_name, arg_ty in cargs
                                ],
                                _canonicalize_measure_references(crtype, name, measures),
                                mk_tuple,
                                cdecs,
                                merged_c_rf,
                                c_decr,
                                loc=cloc,
                            )
                            defs.append(de)

                            # ─── Auto-generated projections (one per named field) ──────
                            # For each constructor field, emit an uninterpreted
                            # polymorphic projection
                            # ``<Type>_<Ctor>_<fname> : forall a:B, …, (this: Type a b …) -> fname's type``.
                            # The SMT layer (``_specialize_liquid_term``)
                            # monomorphises per call site, so references like
                            # ``feats (Pair_mk_fst p)`` in a refinement become
                            # an SMT-tracked equality the solver can chain
                            # through ``Pair_mk_fst`` across consecutive uses.
                            #
                            # Refinement parametricity (preserving refinements
                            # on a constructed value's fields through the
                            # projection) would need covariant subtyping on
                            # TypeConstructor args and is a separate follow-up.
                            this_arg_types: list[SType] = [STypeVar(tv) for tv in args]
                            this_type: SType = STypeConstructor(name, this_arg_types)
                            proj_foralls: list[tuple[Name, Kind]] = [(tv, Kind.BASE) for tv in args]
                            for field_idx, (fname, fty) in enumerate(cargs):
                                proj_name = Name(f"{name.name}_{cname.name}_{fname.name}", fresh_counter.fresh())
                                this_name = Name("this", fresh_counter.fresh())
                                proj_de = Definition(
                                    name=proj_name,
                                    foralls=list(proj_foralls),
                                    args=[(this_name, this_type)],
                                    type=fty,
                                    body=uninterpreted_lit,
                                    decorators=[],
                                    rforalls=[],
                                    decreasing_by=[],
                                    loc=cloc,
                                )
                                defs.append(proj_de)

                def curry(args: list[tuple[Name, SType]], rty: SType, mults: tuple[Multiplicity, ...] = ()) -> SType:
                    n = len(args)
                    for i, (aname, aty) in enumerate(args[::-1]):
                        # ``mults`` is in original (forward) order; index back through it.
                        idx = n - 1 - i
                        m = mults[idx] if idx < len(mults) else MOmega
                        rty = SAbstractionType(aname, aty, rty, multiplicity=m)
                    return rty

                # Emit the recursor body as a Python *expression* (chain of
                # conditional expressions) rather than a `match` statement,
                # so it round-trips cleanly through `eval` at runtime.
                def branch_for(cname: Name, cargs: list[tuple[Name, SType]]) -> tuple[str, str]:
                    body = f"case_{cname.name}" + "".join(f"(this[{i + 1}])" for i in range(len(cargs)))
                    guard = f"this[0] == '{key_for(name, cname)}'"
                    return body, guard

                branches = [branch_for(cons.name, cons.args) for cons in constructors]
                # Catchall raises via a generator-throw trick so it remains an expression.
                rec_expr = "(_ for _ in ()).throw(Exception('Invalid constructor'))"
                for body, guard in reversed(branches):
                    rec_expr = f"({body} if {guard} else {rec_expr})"
                rec_body: STerm = SApplication(SVar(Name("native", 0)), SLiteral(rec_expr, st_string))

                foralls: list[tuple[Name, Kind]] = [(a, Kind.BASE) for a in args]
                rec_args: list[tuple[Name, SType]] = []

                # Return Type
                return_generic_name = Name("ret", -1)
                return_type = STypeVar(return_generic_name)
                foralls.append((return_generic_name, Kind.BASE))

                # Target Type (First argument)
                target_type = STypeConstructor(name, [STypeVar(a) for a in args])
                rec_args.append((Name("this", -1), target_type))

                # Prepare arguments for each constructor. Constructor
                # parameter multiplicities flow through into the
                # corresponding handler abstraction so QTT-discipline
                # destructuring (``match`` over an inductive whose
                # constructors carry ``(1 …)`` fields) works correctly.
                for cons in constructors:
                    rec_args.append(
                        (
                            Name(f"case_{cons.name.name}", -1),
                            curry(cons.args, return_type, cons.arg_multiplicities),
                        )
                    )

                rec_de = Definition(
                    name=Name(name.name + "_rec", -1),
                    foralls=foralls,
                    args=rec_args,
                    type=return_type,
                    body=rec_body,
                    decorators=[],
                    rforalls=list(dtype_rfs),
                    decreasing_by=[],
                    loc=loc,
                )
                defs.append(rec_de)

            case _:
                assert False, f"Unexpected inductive decl {decl} in {p}"

    return Program(
        p.imports,
        p.type_decls + tds,
        [],
        defs + p.definitions,
        p.class_decls,
        p.instance_decls,
        p.export_names,
        p.reexports,
    )
