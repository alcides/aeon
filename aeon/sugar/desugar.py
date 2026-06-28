from __future__ import annotations

from dataclasses import replace
from typing import NamedTuple

from aeon.core.multiplicity import MOmega, Multiplicity
from aeon.core.types import Kind
from aeon.decorators import apply_decorators, collect_core_decorator_queue, Metadata
from aeon.elaboration.context import (
    ElabUninterpretedBinder,
    ElabVariableBinder,
    ElaborationTypingContext,
    ElabTypingContextEntry,
    build_typing_context,
)
from aeon.prelude.prelude import typing_vars
from aeon.sugar.program import (
    Decorator,
    Definition,
    SAbstraction,
    SAnonConstructor,
    SApplication,
    SAnnotation,
    SHole,
    SImplicitRefinementHole,
    SBy,
    SLiteral,
    SIf,
    SQualifiedVar,
    SMethodSelector,
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
from aeon.sugar.program import ClassMethod, InstanceMethod
from aeon.sugar.program import ClassDecl, InstanceDecl
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
from aeon.sugar.substitutions import (
    substitute_svartype_in_stype_by_name,
    substitution_svartype_in_sterm_by_name,
)
from aeon.utils.name import Name, fresh_counter
from aeon.sugar.ast_helpers import st_int, st_string, st_unit, st_bool
from aeon.sugar.instance_registry import InstanceInfo, register_instance

from aeon.sugar.equality import type_equality


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
        return isinstance(cur, SVar) and cur.name == fname

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


def _is_reflection_marker(t: STerm) -> bool:
    return isinstance(t, SVar) and t.name.name == "_"


def _expand_reflection_marker(t: STerm, binder: Name, body: STerm) -> tuple[STerm, int]:
    """Replace each ``_`` marker inside a refinement with ``binder == body``.

    Returns the rewritten term and the number of markers expanded.
    """
    if _is_reflection_marker(t):
        loc = t.loc
        eq = SApplication(
            SApplication(SVar(Name("==", 0), loc=loc), SVar(binder, loc=loc), loc=loc),
            body,
            loc=loc,
        )
        return eq, 1
    match t:
        case SApplication(fun, arg, loc):
            nf, c1 = _expand_reflection_marker(fun, binder, body)
            na, c2 = _expand_reflection_marker(arg, binder, body)
            return SApplication(nf, na, loc=loc), c1 + c2
        case SIf(cond, then, otherwise, loc):
            nc, c1 = _expand_reflection_marker(cond, binder, body)
            nt, c2 = _expand_reflection_marker(then, binder, body)
            no, c3 = _expand_reflection_marker(otherwise, binder, body)
            return SIf(nc, nt, no, loc=loc), c1 + c2 + c3
        case SAnnotation(expr, ty, loc):
            ne, c1 = _expand_reflection_marker(expr, binder, body)
            return SAnnotation(ne, ty, loc=loc), c1
        case _:
            return t, 0


def _mentions_function(body: STerm, fname: Name) -> bool:
    """Whether ``fname`` appears free in ``body`` (used to detect self-recursion).

    Must traverse every construct a reflectable body can take; otherwise a
    recursive call hidden inside an ``if``/``let``/``match`` slips past the
    self-reference check and reaches the solver as an unprovable constraint.
    """
    match body:
        case SVar(name, _):
            return name.name == fname.name
        case SApplication(fun, arg, _):
            return _mentions_function(fun, fname) or _mentions_function(arg, fname)
        case SAnnotation(expr, _, _):
            return _mentions_function(expr, fname)
        case SIf(cond, then, otherwise, _):
            return (
                _mentions_function(cond, fname)
                or _mentions_function(then, fname)
                or _mentions_function(otherwise, fname)
            )
        case SLet(_, val, inner, _) | SRec(_, _, val, inner, _, _):
            return _mentions_function(val, fname) or _mentions_function(inner, fname)
        case STypeApplication(expr, _, _) | SRefinementApplication(expr, _, _):
            return _mentions_function(expr, fname)
        case SAbstraction(_, inner, _):
            return _mentions_function(inner, fname)
        case SMatch(scrutinee, branches, _):
            return _mentions_function(scrutinee, fname) or any(_mentions_function(b.body, fname) for b in branches)
        case _:
            return False


def _is_native_or_uninterpreted_body(body: STerm) -> bool:
    match body:
        case SVar(Name("uninterpreted", _)):
            return True
        case SApplication(SVar(Name("native", _)), _):
            return True
        case SApplication(SVar(Name("native_import", _)), _):
            return True
    return False


def _unreflectable_construct(body: STerm) -> str | None:
    """Name the first body construct that cannot appear in a liquid refinement, or None.

    Reflection via `_` strengthens the return type with ``binder == body``, so the
    body has to be a liquid term (variables, literals, applications, and
    ``if``/``then``/``else`` which lowers to ``ite``). ``match`` and binders
    (``let``/``\\``) are not yet supported.
    """
    match body:
        case SVar() | SLiteral() | SQualifiedVar() | SHole():
            return None
        case SAnnotation(expr, _, _):
            return _unreflectable_construct(expr)
        case SApplication(fun, arg, _):
            return _unreflectable_construct(fun) or _unreflectable_construct(arg)
        case SIf(cond, then, otherwise, _):
            return (
                _unreflectable_construct(cond) or _unreflectable_construct(then) or _unreflectable_construct(otherwise)
            )
        case SMatch():
            return "match"
        case SLet() | SRec():
            return "let"
        case SAbstraction():
            return "lambda"
        case _:
            return type(body).__name__


def reflect_underscore_in_definitions(defs: list[Definition]) -> list[Definition]:
    """Expand the ``_`` reflection marker in each definition's return-type refinement.

    ``def f (x:Int) : {y:Int | _} = x + x`` strengthens the return type to
    ``{y:Int | y == x + x}``, reflecting the body into the predicate.
    """
    out: list[Definition] = []
    for d in defs:
        rtype = d.type
        if not isinstance(rtype, SRefinedType) or any(n.name == "_" for n, _ in d.args):
            out.append(d)
            continue
        new_ref, count = _expand_reflection_marker(rtype.refinement, rtype.name, d.body)
        if count == 0:
            out.append(d)
            continue
        if _is_native_import_def(d) or _is_native_or_uninterpreted_body(d.body):
            raise TypeError(
                f"Cannot reflect the body of '{d.name.name}' with `_`: native and uninterpreted "
                "functions have no encodable implementation."
            )
        if _mentions_function(d.body, d.name):
            raise TypeError(
                f"Cannot reflect the recursive body of '{d.name.name}' with `_`: "
                "self-referential reflection would require inductive reasoning (see issue #328). "
                "Instead, state the recurrence explicitly in the return refinement "
                "(e.g. `: {r:Int | r == n + n} decreasing_by [n]`), which the recursive "
                "call's declared type discharges soundly."
            )
        bad = _unreflectable_construct(d.body)
        if bad is not None:
            raise TypeError(
                f"Cannot reflect the body of '{d.name.name}' with `_`: "
                f"'{bad}' is not expressible in a refinement predicate."
            )
        out.append(replace(d, type=SRefinedType(rtype.name, rtype.type, new_ref, loc=rtype.loc)))
    return out


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
    constructor_to_type: dict[str, Name]
    constructor_defs: dict[str, Name]
    inductive_decls: list[InductiveDecl]
    local_inductive_decls: list[InductiveDecl]


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
        case (
            SLiteral()
            | SVar()
            | SHole()
            | SImplicitRefinementHole()
            | SQualifiedVar()
            | SAnonConstructor()
            | SMethodSelector()
        ):
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
                nbrs.append(
                    SMatchBranch(
                        constructor=br.constructor, binders=br.binders, body=nb, qualifier=br.qualifier, loc=br.loc
                    )
                )
            return SMatch(ns, nbrs, loc=loc), acc
        case SLet(name, val, body, loc=loc):
            nv, s1 = lower_by_blocks_in_sterm(val)
            nb, s2 = lower_by_blocks_in_sterm(body)
            return SLet(name, nv, nb, loc=loc, multiplicity=t.multiplicity), merge(s1, s2)
        case SRec(name, ty, val, body, decreasing_by, loc=loc):
            nv, s1 = lower_by_blocks_in_sterm(val)
            nb, s2 = lower_by_blocks_in_sterm(body)
            decr_parts = [lower_by_blocks_in_sterm(m) for m in decreasing_by]
            nd = tuple(p[0] for p in decr_parts)
            s_decr: dict[Name, tuple[str, ...]] = {}
            for _, sd in decr_parts:
                s_decr = merge(s_decr, sd)
            return (
                SRec(name, ty, nv, nb, decreasing_by=nd, loc=loc, multiplicity=t.multiplicity),
                merge(merge(s1, s2), s_decr),
            )
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
                        arg_multiplicities=d.arg_multiplicities,
                        instance_flags=d.instance_flags,
                    )
                )
            case _:
                assert False, f"lower_by_blocks_in_definitions: {d}"
    return new_definitions, metadata


def resolve_qualified_names_in_sterm(
    t: STerm,
    qualified_scope: QualifiedScope,
    unqualified_scope: UnqualifiedScope,
    constructor_defs: dict[str, Name] | None = None,
    bound: frozenset[str] = frozenset(),
) -> STerm:
    """Replace SQualifiedVar nodes with SVar, and resolve unqualified bare names.

    ``bound`` is the set of names bound by an enclosing binder (function
    parameter, ``let``, ``fun``, ``match`` pattern, ...). A bare variable that
    is locally bound is *never* rewritten to an imported definition — so a
    library's own parameter (e.g. ``NN``'s ``target``) cannot be captured by a
    same-named export of another imported module (e.g. ``Learning.target``).
    Together with the module-prefixing of each library's own top-level
    references, this keeps imported modules from interfering with one another.
    """

    def rec(node: STerm, extra: frozenset[str] = frozenset()) -> STerm:
        return resolve_qualified_names_in_sterm(
            node, qualified_scope, unqualified_scope, constructor_defs, bound | extra
        )

    match t:
        case SAnonConstructor(cname, loc=loc):
            if constructor_defs and cname in constructor_defs:
                return SVar(constructor_defs[cname], loc=loc)
            return t
        case SQualifiedVar(qualifier, name, loc):
            key = (qualifier, name.name)
            if key in qualified_scope:
                return SVar(qualified_scope[key], loc=loc)
            # ``qualifier.name`` where ``qualifier`` names no module or type:
            # treat it as a method call ``qualifier.name`` on a (local)
            # variable ``qualifier`` (issue #27). Since the lexer collapses
            # ``x.m`` into a single QUALIFIED_ID, this is the only place a
            # variable-receiver method call can be recovered. Elaboration
            # resolves it against the receiver's type; if ``qualifier`` is not a
            # bound variable either, it raises there.
            if qualifier not in {q for (q, _) in qualified_scope}:
                return SApplication(SMethodSelector(name, loc=loc), SVar(Name(qualifier), loc=loc), loc=loc)
            raise NameError(f"Name '{name.name}' not found in module '{qualifier}'")
        case SVar(name, loc) if name.name in unqualified_scope and name.name not in bound:
            return SVar(unqualified_scope[name.name], loc=loc)
        case SApplication(fun, arg, loc):
            return SApplication(rec(fun), rec(arg), loc=loc)
        case SAbstraction(name, body, loc):
            return SAbstraction(name, rec(body, frozenset({name.name})), loc=loc)
        case SLet(name, val, body, loc):
            # ``val`` is in the outer scope; ``name`` is bound only in ``body``.
            return SLet(name, rec(val), rec(body, frozenset({name.name})), loc=loc, multiplicity=t.multiplicity)
        case SRec(name, ty, val, body, decreasing_by, loc):
            # ``name`` is recursively bound in its own value and the body. Its
            # type ascription can carry refinements that mention imports
            # (``a : {x:_ | Array.size x = 5} := ...``), so resolve it too.
            inner = frozenset({name.name})
            nd = tuple(rec(m, inner) for m in decreasing_by)
            nty = resolve_qualified_names_in_stype(ty, qualified_scope, unqualified_scope, constructor_defs, bound)
            return SRec(
                name, nty, rec(val, inner), rec(body, inner), decreasing_by=nd, loc=loc, multiplicity=t.multiplicity
            )
        case SIf(cond, then, otherwise, loc):
            return SIf(rec(cond), rec(then), rec(otherwise), loc=loc)
        case SAnnotation(expr, ty, loc):
            nty = resolve_qualified_names_in_stype(ty, qualified_scope, unqualified_scope, constructor_defs, bound)
            return SAnnotation(rec(expr), nty, loc=loc)
        case STypeApplication(body, ty, loc):
            return STypeApplication(rec(body), ty, loc=loc)
        case SRefinementApplication(body, refinement, loc):
            return SRefinementApplication(rec(body), rec(refinement), loc=loc)
        case STypeAbstraction(name, kind, body, loc):
            return STypeAbstraction(name, kind, rec(body), loc=loc)
        case SRefinementAbstraction(pname, sort, body, loc):
            return SRefinementAbstraction(pname, sort, rec(body), loc=loc)
        case SMatch(scrutinee, branches, loc):
            return SMatch(
                scrutinee=rec(scrutinee),
                branches=[
                    SMatchBranch(
                        constructor=br.constructor,
                        binders=br.binders,
                        body=rec(br.body, frozenset(b.name for b in br.binders)),
                        qualifier=br.qualifier,
                        loc=br.loc,
                    )
                    for br in branches
                ],
                loc=loc,
            )
        case _:
            return t


def resolve_qualified_names_in_stype(
    ty: SType,
    qualified_scope: QualifiedScope,
    unqualified_scope: UnqualifiedScope,
    constructor_defs: dict[str, Name] | None = None,
    bound: frozenset[str] = frozenset(),
) -> SType:
    """Resolve qualified names inside refinement predicates within types.

    ``bound`` carries the names bound by enclosing refinement binders and
    dependent-function parameters, so a refinement variable (e.g. ``v`` in
    ``{v: T | ...}`` or the ``rows`` parameter of a dependent type) is never
    rewritten to a same-named import.
    """

    def rec_ty(t: SType, extra: frozenset[str] = frozenset()) -> SType:
        return resolve_qualified_names_in_stype(t, qualified_scope, unqualified_scope, constructor_defs, bound | extra)

    def rec_term(t: STerm, extra: frozenset[str] = frozenset()) -> STerm:
        return resolve_qualified_names_in_sterm(t, qualified_scope, unqualified_scope, constructor_defs, bound | extra)

    match ty:
        case SRefinedType(name, inner_ty, refinement, loc):
            # ``name`` is the refinement's self binder, in scope in the predicate.
            return SRefinedType(name, rec_ty(inner_ty), rec_term(refinement, frozenset({name.name})), loc=loc)
        case SAbstractionType(var_name, var_type, body_type, loc):
            # Dependent: ``var_name`` is bound in the codomain.
            return SAbstractionType(
                var_name,
                rec_ty(var_type),
                rec_ty(body_type, frozenset({var_name.name})),
                loc=loc,
                multiplicity=ty.multiplicity,
            )
        case STypePolymorphism(name, kind, body, loc):
            return STypePolymorphism(name, kind, rec_ty(body), loc=loc)
        case SRefinementPolymorphism(name, sort, body, loc):
            return SRefinementPolymorphism(name, rec_ty(sort), rec_ty(body), loc=loc)
        case STypeConstructor(name, args, loc):
            new_args = [rec_ty(a) for a in args]
            return STypeConstructor(name, new_args, loc=loc)
        case _:
            return ty


def resolve_qualified_names_in_definition(
    d: Definition,
    qualified_scope: QualifiedScope,
    unqualified_scope: UnqualifiedScope,
    constructor_defs: dict[str, Name] | None = None,
) -> Definition:
    # The parameters bind names in the body and the return type; an argument
    # type sees the *preceding* parameters (dependent function types). Seeding
    # ``bound`` here is what stops a parameter name from being captured by a
    # same-named import (e.g. ``NN``'s ``target`` vs ``Learning.target``).
    arg_names = frozenset(name.name for name, _ in d.args)
    new_body = resolve_qualified_names_in_sterm(d.body, qualified_scope, unqualified_scope, constructor_defs, arg_names)
    new_args = []
    seen_args: frozenset[str] = frozenset()
    for name, ty in d.args:
        new_args.append(
            (
                name,
                resolve_qualified_names_in_stype(ty, qualified_scope, unqualified_scope, constructor_defs, seen_args),
            )
        )
        seen_args = seen_args | {name.name}
    new_type = (
        resolve_qualified_names_in_stype(d.type, qualified_scope, unqualified_scope, constructor_defs, arg_names)
        if d.type
        else d.type
    )
    new_decorators = [
        Decorator(
            name=dec.name,
            macro_args=[
                resolve_qualified_names_in_sterm(a, qualified_scope, unqualified_scope, constructor_defs)
                for a in dec.macro_args
            ],
            named_args={
                k: resolve_qualified_names_in_sterm(v, qualified_scope, unqualified_scope, constructor_defs)
                for k, v in dec.named_args.items()
            },
            loc=dec.loc,
        )
        for dec in d.decorators
    ]
    # The termination-metric expressions reference the parameters and measures
    # (e.g. ``size xs``) and must be qualified-name-resolved exactly like the
    # body — otherwise a measure name (``size``) is left unresolved and the
    # termination obligation is undischarged. ``arg_names`` is bound so the
    # parameters are not captured by a same-named import.
    new_decreasing = [
        resolve_qualified_names_in_sterm(m, qualified_scope, unqualified_scope, constructor_defs, arg_names)
        for m in d.decreasing_by
    ]
    if (
        new_body is d.body
        and new_args == d.args
        and new_type is d.type
        and new_decorators == d.decorators
        and new_decreasing == list(d.decreasing_by)
    ):
        return d
    return Definition(
        d.name,
        d.foralls,
        new_args,
        new_type,
        new_body,
        new_decorators,
        d.rforalls,
        new_decreasing,
        d.loc,
        arg_multiplicities=d.arg_multiplicities,
        instance_flags=d.instance_flags,
    )


def desugar(
    p: Program,
    is_main_hole: bool = True,
    extra_vars: dict[Name, SType] | None = None,
    *,
    compiled_imports: dict | None = None,
    module_export_name: str | None = None,
) -> DesugaredProgram:
    dep_units = {} if compiled_imports is None else compiled_imports
    vs: dict[Name, SType] = {} if extra_vars is None else extra_vars
    vs.update(typing_vars)

    # Snapshot ``mutual`` group membership by (stable, already-bound) name before
    # the Definition-rewriting passes below, which do not preserve the field.
    mutual_group_by_name: dict[Name, int] = {
        d.name: d.mutual_group_id for d in p.definitions if d.mutual_group_id is not None
    }

    # Pull class/instance declarations from imported modules into the main
    # program so they are expanded by the single ``expand_typeclasses`` pass
    # below. Typeclass methods resolve by type through the global instance
    # registry rather than by qualified name, so — unlike ordinary library
    # definitions, which ``handle_imports`` module-prefixes — they live
    # directly in the main namespace.
    inductive_names_top = {d.name.name for d in p.inductive_decls}
    imported_classes, imported_instances = collect_imported_typeclasses(p.imports, inductive_names_top, dep_units)
    if imported_classes or imported_instances:
        p = Program(
            p.imports,
            p.type_decls,
            p.inductive_decls,
            p.definitions,
            imported_classes + p.class_decls,
            imported_instances + p.instance_decls,
        )

    # Lower class/instance declarations into inductives + plain definitions
    # before any inductive processing so the generated dictionary types flow
    # through the normal pipeline.
    p = expand_typeclasses(p)

    # We need inductive constructor info to lower `match` expressions.
    # Note: `expand_inductive_decls` clears `p.inductive_decls`, so we snapshot it here.
    p = infer_inductive_rforall_decls(p)
    inductive_decls_snapshot = list(p.inductive_decls)

    p = expand_inductive_decls(p)

    prog = determine_main_function(p, is_main_hole)

    defs, type_decls = p.definitions, p.type_decls

    # Separate "open InductiveType" from file imports
    inductive_names = {decl.name.name for decl in inductive_decls_snapshot}
    file_imports = []
    open_inductives: set[str] = set()
    for imp in p.imports:
        if imp.is_open and imp.module_path in inductive_names:
            open_inductives.add(imp.module_path)
        else:
            file_imports.append(imp)

    if not dep_units and file_imports:
        from aeon.compilation.compile import compile_imports_for_desugar

        dep_units = compile_imports_for_desugar(file_imports)

    defs, type_decls, imported_inductives, qualified_scope, unqualified_scope = handle_imports_from_units(
        file_imports, defs, type_decls, dep_units
    )

    # ``native_import`` definitions bind a global Python symbol (e.g. ``np``)
    # that *other* modules' native bodies reference by bare name. The runtime
    # builds a let-chain from ``defs`` (first entry = outermost binding), and a
    # closure only captures bindings introduced before it. When a third module
    # re-imports a provider (e.g. ``Learning`` selectively imports ``Tensor``),
    # the import walk can place a consumer (``NN.dense_relu``, whose native uses
    # ``np``) ahead of its provider (``Tensor``'s ``np``), so the consumer's
    # closure would not see it. Hoisting every ``native_import`` to the front —
    # they are side-effecting, dependency-free imports — makes those globals
    # available to every definition regardless of import order.
    defs = [d for d in defs if _is_native_import_def(d)] + [d for d in defs if not _is_native_import_def(d)]

    # Folded snapshot used to lower `match` expressions everywhere — main module's
    # inductives plus inductives discovered via imports.
    combined_inductives = list(inductive_decls_snapshot) + list(imported_inductives)

    # Collapse duplicate type declarations sharing a name. When two libraries
    # declare the "same" name with different arities (e.g. libraries/List.ae's
    # ``type List a`` and libraries/PSB2.ae's ``type List``), keep the
    # parametric one; bare uses of the name in either file are expanded with
    # fresh args below by ``expand_bare_parametric_type_ctors``.
    type_decls = _dedupe_type_decls(type_decls)

    # Register inductive constructors for qualified access (e.g. IntList.cons)
    # and build constructor_to_type / constructor_defs mappings
    constructor_to_type: dict[str, Name] = {}
    constructor_defs: dict[str, Name] = {}
    for decl in combined_inductives:
        for cons in decl.constructors:
            prefixed = Name(f"{decl.name.name}_{cons.name.name}", cons.name.id)
            qualified_scope[(decl.name.name, cons.name.name)] = prefixed
            constructor_to_type[cons.name.name] = decl.name
            constructor_defs[cons.name.name] = prefixed
            # "open IntList" brings constructors into bare scope
            if decl.name.name in open_inductives:
                unqualified_scope[cons.name.name] = prefixed

    # Register dotted definition names ``def Type.method`` for qualified access
    # (issue #27), so ``Type.method`` resolves to the same binder that a method
    # call ``recv.method`` dispatches to during elaboration.
    for d in defs:
        if "." in d.name.name:
            qualifier, _, bare = d.name.name.rpartition(".")
            qualified_scope[(qualifier, bare)] = d.name

    if module_export_name is not None:
        local_qualified: QualifiedScope = dict(qualified_scope)
        local_unqualified: UnqualifiedScope = dict(unqualified_scope)
        defs = build_module_scopes(defs, module_export_name, local_qualified, local_unqualified, combined_inductives)
        qualified_scope.update(local_qualified)
        unqualified_scope.update(local_unqualified)
        _refresh_inductive_constructor_scopes(
            combined_inductives, defs, module_export_name, qualified_scope, constructor_defs
        )
    else:
        defs = [
            resolve_qualified_names_in_definition(d, qualified_scope, unqualified_scope, constructor_defs) for d in defs
        ]
    prog = resolve_qualified_names_in_sterm(prog, qualified_scope, unqualified_scope, constructor_defs)

    # Expand the `_` reflection marker in return-type refinements into `binder == body`.
    defs = reflect_underscore_in_definitions(defs)
    defs, metadata = apply_decorators_in_definitions(defs)
    defs, metadata = lower_by_blocks_in_definitions(defs, metadata)

    defs = expand_bare_parametric_type_ctors(defs, type_decls)
    defs = introduce_forall_in_types(defs, type_decls)
    defs = introduce_rforall_in_types(defs)

    defs, metadata = collect_core_decorator_queue(defs, metadata)

    # The many Definition-rewriting passes above don't preserve ``mutual_group_id``;
    # reattach it by name (names are stable after binding) so the SRec chain builder
    # can recover each ``mutual`` group.
    if mutual_group_by_name:
        defs = [
            d
            if d.mutual_group_id is not None or d.name not in mutual_group_by_name
            else replace(d, mutual_group_id=mutual_group_by_name[d.name])
            for d in defs
        ]

    etctx = build_typing_context(vs, type_decls, constructor_to_type, constructor_defs)
    if dep_units:
        etctx = extend_elabcontext_with_imports(etctx, file_imports, dep_units)
    imported_type_names: list[Name] = []
    seen_type_names: set[str] = set()

    def _add_type_name(name: Name) -> None:
        if name.name not in seen_type_names:
            imported_type_names.append(name)
            seen_type_names.add(name.name)

    for unit in dep_units.values():
        for decl in unit.inductive_decls:
            _add_type_name(decl.name)
        for td in unit.type_decls:
            _add_type_name(td.name)
    type_names = [Name(t, 0) for t in builtin_types]
    for name in imported_type_names + [td.name for td in type_decls] + [decl.name for decl in combined_inductives]:
        _add_type_name(name)
    defs = _canonicalize_definition_types(defs, type_names)
    etctx, prog = update_program_and_context(prog, defs, etctx)
    prog, etctx = replace_concrete_types(prog, etctx, type_names)
    prog, etctx = canonicalize_imported_type_constructors(prog, etctx, type_names)
    # Lower match expressions (Lean syntax) into the generated inductive eliminators.
    # Use the folded snapshot so matches inside imported library bodies are also lowered.
    prog = lower_match_to_inductive_rec(prog, combined_inductives)
    return DesugaredProgram(
        prog, etctx, metadata, constructor_to_type, constructor_defs, combined_inductives, inductive_decls_snapshot
    )


def lower_match_to_inductive_rec(prog: STerm, inductive_decls: list[InductiveDecl]) -> STerm:
    """
    Rewrite `match scrutinee with | C x y => e | ...` into:
        <Inductive>_rec scrutinee (fun x => fun y => e) ...
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
                cons_names = [b.constructor for b in branches]

                # If any branch has a qualifier, use it to directly select the inductive.
                chosen: Name | None = None
                chosen_cons_map: dict[Name, list[tuple[Name, SType]]] | None = None
                for br in branches:
                    if br.qualifier is not None:
                        for iname, cmap in inductive_info.items():
                            if iname.name == br.qualifier:
                                chosen = iname
                                chosen_cons_map = cmap
                                break
                        break

                # Fall back: find the first inductive that contains all branch constructors.
                if chosen is None:
                    for iname, cmap in inductive_info.items():
                        if all(cn in cmap for cn in cons_names):
                            chosen = iname
                            chosen_cons_map = cmap
                            break

                if chosen is None or chosen_cons_map is None:
                    # Fall back: this should typically be rejected by typechecking later.
                    return SMatch(lowered_scrut, branches, loc=t.loc)

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
                                for b in branches:
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
                return SLet(name, lower_term(val), lower_term(body), loc=loc, multiplicity=t.multiplicity)
            case SRec(name, ty, val, body, decreasing_by, loc=loc):
                nd = tuple(lower_term(m) for m in decreasing_by)
                return SRec(
                    name,
                    ty,
                    lower_term(val),
                    lower_term(body),
                    decreasing_by=nd,
                    loc=loc,
                    multiplicity=t.multiplicity,
                    mutual_group_id=t.mutual_group_id,
                    companions=t.companions,
                )
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


def _merge_inductive_rforalls(
    dtype_rfs: list[tuple[Name, SType]], local_rfs: list[tuple[Name, SType]]
) -> list[tuple[Name, SType]]:
    """Datatype-level abstract refinements (Liquid Haskell ``data T <p>``) scope over every constructor."""
    seen = {n for n, _ in dtype_rfs}
    return list(dtype_rfs) + [(n, t) for n, t in local_rfs if n not in seen]


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
                case SApplication(SVar(p), SVar(b)) if b == binder and p not in bound_rho:
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


class TypeClassError(Exception):
    """Raised when a class/instance declaration is malformed (unknown class,
    missing method, etc.)."""


def _mangle_stype(ty: SType) -> str:
    """A flat identifier-safe rendering of a type, used to name instance dicts."""
    match ty:
        case STypeVar(name):
            return name.name
        case STypeConstructor(name, args):
            if not args:
                return name.name
            return name.name + "_" + "_".join(_mangle_stype(a) for a in args)
        case _:
            return "t"


def _stype_head_name(ty: SType) -> str | None:
    """Outermost type-constructor (or type-variable) name of a type, used to key
    the instance database. ``Int`` → "Int", ``List a`` → "List", ``a`` → "a"."""
    match ty:
        case STypeConstructor(name, _):
            return name.name
        case STypeVar(name):
            return name.name
        case _:
            return None


def _curry_lambda(binders: list[Name], body: STerm) -> STerm:
    """Wrap ``body`` in nested lambdas, one per binder (left-to-right)."""
    for b in reversed(binders):
        body = SAbstraction(b, body)
    return body


def expand_typeclasses(p: Program) -> Program:
    """Lower ``class``/``instance`` declarations to inductives + plain definitions.

    A ``class C (a : k) where m_i : T_i [:= d_i]`` becomes:
      * an inductive ``C a`` with a single constructor ``C_mk`` whose fields are
        the method types — dependent, so a later field's refinement may mention an
        earlier method (this is how refinement *laws* are encoded); and
      * one projection ``def m_i : forall a, [d : C a] -> T_i = native "d[i+1]"``
        that pulls field ``i`` out of the runtime dictionary tuple
        ``('C_mk', f0, f1, …)``.

    An ``instance [Ck a]… : C T where m_i bs := e_i`` becomes a dictionary
    definition ``def <name> : C T = C_mk impl_0 … impl_n`` where each ``impl_i``
    is the supplied body (curried over its binders) or the class default when the
    method is omitted. Instance constraints become instance-implicit parameters.
    """
    if not p.class_decls and not p.instance_decls:
        return p

    # Generated projection / dictionary definitions must precede user code that
    # references them: aeon resolves names define-before-use, so we prepend.
    new_inductives: list[InductiveDecl] = list(p.inductive_decls)
    gen_defs: list[Definition] = []

    class_methods: dict[str, list[ClassMethod]] = {}

    for cls in p.class_decls:
        cname = cls.name
        type_param_names = [n for (n, _) in cls.type_params]
        class_methods[cname.name] = list(cls.methods)

        ret_type = STypeConstructor(cname, [STypeVar(n) for n in type_param_names])

        # Unprefixed constructor name ``mk``; ``expand_inductive_decls`` namespaces
        # it to ``<Class>_mk``. The dictionary is built by referencing it through
        # ``SQualifiedVar(<Class>, mk)`` (resolved per-class during desugaring).
        cons = Definition(
            name=Name("mk"),
            foralls=[],
            args=[(m.name, m.type) for m in cls.methods],
            type=ret_type,
            body=SLiteral(None, st_unit),
            loc=cls.loc,
        )
        new_inductives.append(
            InductiveDecl(
                name=cname,
                args=list(type_param_names),
                rforalls=[],
                constructors=[cons],
                measures=[],
                loc=cls.loc,
            )
        )

        foralls: list[tuple[Name, Kind]] = [(n, k) for (n, k) in cls.type_params]
        for i, m in enumerate(cls.methods):
            dict_name = Name(f"_d{fresh_counter.fresh()}")
            # Eta-expand the projection: peel the method type's leading arrows
            # into explicit ``args`` so the projection's *return* type is a base
            # (or refined) type rather than a function type. A ``native`` whose
            # return type is itself a polymorphic function type fails to
            # elaborate (the type-variable would be instantiated with a function
            # type, which cannot carry the inserted refinement). Applying the
            # dictionary field to the peeled binders sidesteps that entirely.
            peeled: list[tuple[Name, SType]] = []
            ret_t: SType = m.type
            while isinstance(ret_t, SAbstractionType):
                peeled.append((ret_t.var_name, ret_t.var_type))
                ret_t = ret_t.type
            call = f"{dict_name.name}[{i + 1}]" + "".join(f"({pn.name})" for (pn, _) in peeled)
            gen_defs.append(
                Definition(
                    name=m.name,
                    foralls=list(foralls),
                    args=[(dict_name, ret_type), *peeled],
                    type=ret_t,
                    body=SApplication(
                        SVar(Name("native", 0)),
                        SLiteral(call, st_string),
                    ),
                    loc=m.loc,
                    instance_flags=(True, *(False for _ in peeled)),
                )
            )

    def _concretize_head(ty: SType, bound: set[str]) -> SType:
        """Resolve a bare type name in an instance head to a constructor.

        The parser turns every non-builtin bare identifier into an
        ``STypeVar`` (it has no type registry), so ``instance : C Network``
        would otherwise be read as polymorphic over a variable *named*
        ``Network`` — making the method bodies see an abstract ``'Network``
        that won't unify with the concrete imported type. By Aeon's naming
        convention type variables are lower-case; an upper-case head name
        that is not bound by the instance's own constraints denotes a
        concrete type, so promote it to a (nullary) ``STypeConstructor``.
        Constraint-bound variables (e.g. ``a`` in ``instance [Eq a] : Eq
        (Box a)``) are preserved.
        """
        match ty:
            case STypeVar(name):
                if name.name not in bound and name.name[:1].isupper():
                    return STypeConstructor(name, [])
                return ty
            case STypeConstructor(name, args):
                return STypeConstructor(name, [_concretize_head(a, bound) for a in args], loc=ty.loc)
            case _:
                return ty

    for inst in p.instance_decls:
        methods = class_methods.get(inst.class_name.name)
        if methods is None:
            raise TypeClassError(f"Instance for unknown class '{inst.class_name.name}'")

        # Variables genuinely bound by the instance (those appearing in its
        # constraints) stay variables; other upper-case head names are
        # concrete types. Rewrite the head args once and use throughout.
        constraint_vars: set[str] = set()
        for c in inst.constraints:
            constraint_vars |= {tv.name.name for tv in get_type_vars(c)}
        inst_type_args = [_concretize_head(ta, constraint_vars) for ta in inst.type_args]

        provided: dict[str, InstanceMethod] = {m.name.name: m for m in inst.methods}

        impls: list[STerm] = []
        for m in methods:
            im = provided.get(m.name.name)
            if im is not None:
                binders = [n for (n, _) in im.args]
                impls.append(_curry_lambda(binders, im.body))
            elif m.default is not None:
                impls.append(m.default)
            else:
                raise TypeClassError(f"Instance of '{inst.class_name.name}' is missing method '{m.name.name}'")

        # Instantiate the dictionary constructor at the instance's type
        # arguments (e.g. ``Eq_mk[Int]``) so elaboration can resolve the
        # constructor's ``forall`` binders. The method implementations are
        # lambdas whose parameter types are unknown until ``a`` is fixed, so
        # argument-driven inference alone cannot recover it.
        dict_body: STerm = SQualifiedVar(inst.class_name.name, Name("mk"))
        for ta in inst_type_args:
            dict_body = STypeApplication(dict_body, ta)
        for impl in impls:
            dict_body = SApplication(dict_body, impl)

        dict_type: SType = STypeConstructor(inst.class_name, list(inst_type_args))

        tyvars = set()
        for ta in inst_type_args:
            tyvars |= get_type_vars(ta)
        for c in inst.constraints:
            tyvars |= get_type_vars(c)
        inst_foralls: list[tuple[Name, Kind]] = [
            (tv.name, Kind.BASE) for tv in sorted(tyvars, key=lambda t: t.name.name)
        ]

        constraint_args: list[tuple[Name, SType]] = [(Name(f"_c{fresh_counter.fresh()}"), c) for c in inst.constraints]

        if inst.name is not None:
            dict_def_name = inst.name
        else:
            dict_def_name = Name(f"__inst_{inst.class_name.name}_{'_'.join(_mangle_stype(t) for t in inst_type_args)}")

        gen_defs.append(
            Definition(
                name=dict_def_name,
                foralls=inst_foralls,
                args=constraint_args,
                type=dict_type,
                body=dict_body,
                loc=inst.loc,
                instance_flags=tuple(True for _ in constraint_args),
            )
        )

        if inst_type_args:
            head = _stype_head_name(inst_type_args[0])
            if head is not None:
                register_instance(
                    inst.class_name.name,
                    head,
                    InstanceInfo(
                        dict_name=dict_def_name,
                        foralls=tuple(n for (n, _) in inst_foralls),
                        num_constraints=len(constraint_args),
                        type_args=tuple(inst_type_args),
                        constraints=tuple(inst.constraints),
                    ),
                )

    return Program(p.imports, p.type_decls, new_inductives, gen_defs + list(p.definitions))


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

    return Program(p.imports, p.type_decls, inferred, p.definitions)


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
                                mname,
                                mforalls,
                                margs,
                                mrtype,
                                uninterpreted_lit,
                                mdecs,
                                merged_m_rf,
                                m_decr,
                                loc=mloc,
                            )
                            defs.append(de)

                def key_for(tyname: Name, constructor_name: Name) -> str:
                    return f"{tyname.name}_{constructor_name.name}"

                # Register constructor groups for SMT distinctness assertions
                from aeon.verification.constructor_registry import register_constructors

                register_constructors(name.name, [key_for(name, cons.name) for cons in constructors])

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
                                cargs,
                                crtype,
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

    return Program(p.imports, p.type_decls + tds, [], defs + p.definitions)


def _dedupe_type_decls(decls: list[TypeDecl]) -> list[TypeDecl]:
    """Collapse type declarations that share a name. Preference goes to the
    one with more args, so a parametric ``type List a`` wins over a bare
    ``type List``."""
    by_name: dict[str, TypeDecl] = {}
    order: list[str] = []
    for td in decls:
        existing = by_name.get(td.name.name)
        if existing is None:
            by_name[td.name.name] = td
            order.append(td.name.name)
        elif len(td.args) > len(existing.args):
            by_name[td.name.name] = td
    return [by_name[n] for n in order]


def _expand_bare_parametric_type_ctors_in_stype(
    ty: SType,
    parametric: dict[str, TypeDecl],
    cache: dict[str, STypeConstructor],
) -> SType:
    """Expand bare references to parametric type constructors with fresh type
    variables. With ``type List a`` in scope, a bare ``List`` used as a type
    becomes ``(List _a<n>)``. Each definition shares one fresh-arg tuple per
    parametric type (via ``cache``), so all bare ``List`` occurrences within
    one signature refer to the same element type."""

    def get_replacement(tname: str) -> STypeConstructor:
        if tname not in cache:
            td = parametric[tname]
            fresh_args: list[SType] = [STypeVar(Name(f"_{a.name}", fresh_counter.fresh())) for a in td.args]
            cache[tname] = STypeConstructor(td.name, fresh_args)
        return cache[tname]

    def rec(t: SType) -> SType:
        return _expand_bare_parametric_type_ctors_in_stype(t, parametric, cache)

    match ty:
        case STypeVar(name) if name.name in parametric:
            return get_replacement(name.name)
        case STypeVar(_):
            return ty
        case STypeConstructor(name, args, loc):
            return STypeConstructor(name, [rec(a) for a in args], loc=loc)
        case SAbstractionType(vname, vty, rty, loc):
            return SAbstractionType(vname, rec(vty), rec(rty), loc=loc, multiplicity=ty.multiplicity)
        case SRefinedType(name, ity, ref, loc):
            return SRefinedType(name, rec(ity), ref, loc=loc)
        case STypePolymorphism(name, kind, body, loc):
            return STypePolymorphism(name, kind, rec(body), loc=loc)
        case SRefinementPolymorphism(name, sort, body, loc):
            return SRefinementPolymorphism(name, rec(sort), rec(body), loc=loc)
        case _:
            return ty


def _expand_bare_parametric_type_ctors_in_sterm(
    t: STerm,
    parametric: dict[str, TypeDecl],
    cache: dict[str, STypeConstructor],
) -> STerm:
    """Walk an STerm and expand bare parametric type constructors in any
    embedded SType. Uses a shared cache so all bare ``List`` occurrences
    within one definition share the same fresh type-variable args."""

    def rec_ty(ty: SType) -> SType:
        return _expand_bare_parametric_type_ctors_in_stype(ty, parametric, cache)

    def rec(node: STerm) -> STerm:
        return _expand_bare_parametric_type_ctors_in_sterm(node, parametric, cache)

    match t:
        case SLiteral(val, ty, loc):
            return SLiteral(val, rec_ty(ty), loc=loc)
        case SAnnotation(expr, ty, loc):
            return SAnnotation(rec(expr), rec_ty(ty), loc=loc)
        case SApplication(fun, arg, loc):
            return SApplication(rec(fun), rec(arg), loc=loc)
        case SAbstraction(name, body, loc):
            return SAbstraction(name, rec(body), loc=loc)
        case SLet(name, val, body, loc):
            return SLet(name, rec(val), rec(body), loc=loc, multiplicity=t.multiplicity)
        case SRec(name, ty, val, body, decreasing_by, loc):
            return SRec(
                name,
                rec_ty(ty),
                rec(val),
                rec(body),
                decreasing_by=tuple(rec(m) for m in decreasing_by),
                loc=loc,
                multiplicity=t.multiplicity,
            )
        case SIf(cond, then, otherwise, loc):
            return SIf(rec(cond), rec(then), rec(otherwise), loc=loc)
        case STypeApplication(body, ty, loc):
            return STypeApplication(rec(body), rec_ty(ty), loc=loc)
        case STypeAbstraction(name, kind, body, loc):
            return STypeAbstraction(name, kind, rec(body), loc=loc)
        case SRefinementAbstraction(name, sort, body, loc):
            return SRefinementAbstraction(name, rec_ty(sort), rec(body), loc=loc)
        case SRefinementApplication(body, refinement, loc):
            return SRefinementApplication(rec(body), rec(refinement), loc=loc)
        case SMatch(scrutinee, branches, loc):
            return SMatch(
                scrutinee=rec(scrutinee),
                branches=[
                    SMatchBranch(
                        constructor=br.constructor,
                        binders=br.binders,
                        body=rec(br.body),
                        qualifier=br.qualifier,
                        loc=br.loc,
                    )
                    for br in branches
                ],
                loc=loc,
            )
        case _:
            return t


def expand_bare_parametric_type_ctors(defs: list[Definition], type_decls: list[TypeDecl]) -> list[Definition]:
    parametric = {td.name.name: td for td in type_decls if td.args}
    if not parametric:
        return defs
    ndefs: list[Definition] = []
    for d in defs:
        cache: dict[str, STypeConstructor] = {}
        new_args = [(n, _expand_bare_parametric_type_ctors_in_stype(t, parametric, cache)) for n, t in d.args]
        new_rtype = _expand_bare_parametric_type_ctors_in_stype(d.type, parametric, cache)
        new_body = _expand_bare_parametric_type_ctors_in_sterm(d.body, parametric, cache)
        ndefs.append(
            Definition(
                d.name,
                d.foralls,
                new_args,
                new_rtype,
                new_body,
                d.decorators,
                d.rforalls,
                d.decreasing_by,
                d.loc,
                arg_multiplicities=d.arg_multiplicities,
                instance_flags=d.instance_flags,
            )
        )
    return ndefs


def _collect_type_vars_in_sterm(t: STerm, acc: set[STypeVar], bound: set[Name]) -> None:
    """Walk an STerm and collect every free STypeVar (i.e. not bound by an
    enclosing ``STypeAbstraction``) that appears inside an embedded SType.
    Used by ``introduce_forall_in_types`` so type variables introduced inside
    a definition's body (e.g. by ``expand_bare_parametric_type_ctors`` on
    ``actual_values : List = …``) get promoted to the surrounding
    definition's forall list."""

    def rec(node: STerm) -> None:
        _collect_type_vars_in_sterm(node, acc, bound)

    def add_free(ty: SType) -> None:
        for tv in get_type_vars(ty):
            if tv.name not in bound:
                acc.add(tv)

    match t:
        case SLiteral(_, ty, _):
            add_free(ty)
        case SAnnotation(expr, ty, _):
            add_free(ty)
            rec(expr)
        case SApplication(fun, arg, _):
            rec(fun)
            rec(arg)
        case SAbstraction(_, body, _):
            rec(body)
        case SLet(_, val, body, _):
            rec(val)
            rec(body)
        case SRec(_, ty, val, body, decreasing_by, _):
            add_free(ty)
            rec(val)
            rec(body)
            for m in decreasing_by:
                rec(m)
        case SIf(cond, then, otherwise, _):
            rec(cond)
            rec(then)
            rec(otherwise)
        case STypeApplication(body, ty, _):
            add_free(ty)
            rec(body)
        case STypeAbstraction(tname, _, body, _):
            _collect_type_vars_in_sterm(body, acc, bound | {tname})
        case SRefinementAbstraction(_, sort, body, _):
            add_free(sort)
            rec(body)
        case SRefinementApplication(body, refinement, _):
            rec(body)
            rec(refinement)
        case SMatch(scrutinee, branches, _):
            rec(scrutinee)
            for br in branches:
                rec(br.body)
        case _:
            return


def introduce_forall_in_types(defs: list[Definition], type_decls: list[TypeDecl]) -> list[Definition]:
    type_names = {td.name.name for td in type_decls}
    ndefs = []
    for d in defs:
        match d:
            case Definition(name, foralls, args, rtype, body, decorators, rforalls, decreasing_by, loc):
                new_foralls: list[tuple[Name, Kind]] = []

                bound_tvars = {n for n, _ in foralls}
                tlst: list[SType] = [ty for _, ty in args] + [rtype]
                free_tvars: set[STypeVar] = set()
                for ty in tlst:
                    free_tvars.update(get_type_vars(ty))
                _collect_type_vars_in_sterm(body, free_tvars, bound_tvars)
                bound_tvar_names = {n.name for n in bound_tvars}
                for t in free_tvars:
                    tname = t.name
                    if tname.name not in type_names and tname.name not in bound_tvar_names:
                        entry = (tname, Kind.BASE)
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
                        arg_multiplicities=d.arg_multiplicities,
                        instance_flags=d.instance_flags,
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
                    # The inferred sort is the full predicate type ``base -> Bool``.
                    pred_ty = SAbstractionType(Name("_"), base, st_bool)
                    if p in acc:
                        if acc[p] != pred_ty:
                            raise TypeError(
                                f"Inconsistent sorts for implicit refinement parameter {p.name}: {acc[p]} vs {pred_ty}"
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
                        arg_multiplicities=d.arg_multiplicities,
                        instance_flags=d.instance_flags,
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


def _is_native_import_def(d: Definition) -> bool:
    """Check if a definition's body is a native_import call (side-effect import)."""
    match d.body:
        case SApplication(SVar(Name("native_import", _)), _):
            return True
    return False


def _bare_name(module_name: str, def_name: str) -> str:
    """Strip module prefix from a definition name if present: Math_pow -> pow, or pow -> pow."""
    prefix = module_name + "_"
    if def_name.startswith(prefix):
        return def_name[len(prefix) :]
    return def_name


# Scope entry: maps (qualifier, bare_name) -> prefixed Name for qualified access,
# and bare_name -> prefixed Name for unqualified access (open / selective imports).
ModuleScope = dict[str, Name]  # bare_name -> original Name
QualifiedScope = dict[tuple[str, str], Name]  # (qualifier, bare_name) -> original Name
UnqualifiedScope = dict[str, Name]  # bare_name -> original Name


def collect_imported_typeclasses(
    imports: list[ImportAe],
    inductive_names: set[str],
    compiled_imports: dict,
    _seen: set[str] | None = None,
) -> tuple[list[ClassDecl], list[InstanceDecl]]:
    """Gather ``class``/``instance`` declarations from (transitively) imported modules."""
    seen: set[str] = set() if _seen is None else _seen
    classes: list[ClassDecl] = []
    instances: list[InstanceDecl] = []
    for imp in imports:
        if imp.is_open and imp.module_path in inductive_names:
            continue
        if imp.module_path in seen:
            continue
        seen.add(imp.module_path)
        unit = compiled_imports.get(imp.module_path)
        if unit is None:
            continue
        for dep_module in unit.dependencies:
            dep_unit = compiled_imports.get(dep_module)
            if dep_unit is not None:
                sub_inductive = {d.name.name for d in dep_unit.inductive_decls}
                sub_classes, sub_instances = collect_imported_typeclasses(
                    [ImportAe(module_path=dep_module)],
                    sub_inductive,
                    compiled_imports,
                    seen,
                )
                classes.extend(sub_classes)
                instances.extend(sub_instances)
        classes.extend(unit.class_decls)
        instances.extend(unit.instance_decls)
    return classes, instances


def _refresh_inductive_constructor_scopes(
    inductive_decls: list[InductiveDecl],
    defs: list[Definition],
    module_export_name: str,
    qualified_scope: QualifiedScope,
    constructor_defs: dict[str, Name],
) -> None:
    """After ``build_module_scopes``, align inductive constructor maps with prefixed binders."""
    def_by_name = {d.name.name: d.name for d in defs}
    for decl in inductive_decls:
        for cons in decl.constructors:
            bare = cons.name.name
            candidates = (
                f"{module_export_name}_{decl.name.name}_{bare}",
                f"{decl.name.name}_{bare}",
            )
            internal: Name | None = None
            for candidate in candidates:
                if candidate in def_by_name:
                    internal = def_by_name[candidate]
                    break
            if internal is None:
                continue
            qualified_scope[(decl.name.name, bare)] = internal
            if decl.name.name == module_export_name or decl.name.name.startswith(f"{module_export_name}_"):
                constructor_defs[bare] = internal


def build_module_scopes(
    defs: list[Definition],
    module_name: str,
    qualified_scope: QualifiedScope,
    unqualified_scope: UnqualifiedScope,
    inductive_decls: list[InductiveDecl] | None = None,
) -> list[Definition]:
    local_qualified: QualifiedScope = dict(qualified_scope)
    local_unqualified: UnqualifiedScope = dict(unqualified_scope)
    inductive_names = {decl.name.name for decl in inductive_decls or []}
    for d in defs:
        if _is_native_import_def(d):
            continue
        bare = _bare_name(module_name, d.name.name)
        internal_name = Name(f"{module_name}_{bare}", d.name.id)
        local_qualified[(module_name, bare)] = internal_name
        local_unqualified[bare] = internal_name
        if "_" in bare:
            type_part, ctor_part = bare.rsplit("_", 1)
            if type_part in inductive_names:
                local_qualified[(type_part, ctor_part)] = internal_name

    prefixed: list[Definition] = []
    for d in defs:
        if _is_native_import_def(d):
            prefixed.append(d)
            continue
        bare = _bare_name(module_name, d.name.name)
        internal_name = Name(f"{module_name}_{bare}", d.name.id)
        resolved_d = resolve_qualified_names_in_definition(d, local_qualified, local_unqualified)
        prefixed.append(
            Definition(
                internal_name,
                resolved_d.foralls,
                resolved_d.args,
                resolved_d.type,
                resolved_d.body,
                resolved_d.decorators,
                resolved_d.rforalls,
                resolved_d.decreasing_by,
                resolved_d.loc,
                arg_multiplicities=resolved_d.arg_multiplicities,
                instance_flags=resolved_d.instance_flags,
            )
        )
        qualified_scope[(module_name, bare)] = internal_name
    return prefixed


def extend_elabcontext_with_imports(
    ctx: ElaborationTypingContext,
    imports: list[ImportAe],
    compiled_imports: dict,
) -> ElaborationTypingContext:
    from aeon.elaboration.context import ElabTypeDecl, ElabUninterpretedBinder, ElabVariableBinder
    from aeon.sugar.lifting import lift_type
    from aeon.typechecking.context import UninterpretedBinder

    entries = list(ctx.entries)
    seen: set[Name] = set()
    constructor_to_type = dict(ctx.constructor_to_type)
    constructor_defs = dict(ctx.constructor_defs)

    def add_unit(unit) -> None:
        seen_types: set[str] = {e.name.name for e in entries if isinstance(e, ElabTypeDecl)}
        for td in unit.type_decls:
            if td.name.name not in seen_types:
                entries.append(ElabTypeDecl(td.name, td.args, td.rforalls))
                seen_types.add(td.name.name)
        for decl in unit.inductive_decls:
            if decl.name.name not in seen_types:
                entries.append(ElabTypeDecl(decl.name, decl.args, decl.rforalls))
                seen_types.add(decl.name.name)
        for decl in unit.inductive_decls:
            constructor_to_type.update({cons.name.name: decl.name for cons in decl.constructors})
        constructor_to_type.update(unit.constructor_to_type)
        for export in unit.exports.values():
            if export.internal_name not in seen:
                entries.append(ElabVariableBinder(export.internal_name, export.sugar_type))
                seen.add(export.internal_name)
        for entry in unit.typing_ctx.entries:
            if not isinstance(entry, UninterpretedBinder):
                continue
            if entry.name in seen:
                continue
            entries.append(ElabUninterpretedBinder(entry.name, lift_type(entry.type)))
            seen.add(entry.name)

    visited: set[str] = set()

    def visit_module(module_path: str) -> None:
        if module_path in visited:
            return
        visited.add(module_path)
        unit = compiled_imports.get(module_path)
        if unit is None:
            return
        for dep in unit.dependencies:
            visit_module(dep)
        add_unit(unit)

    for imp in imports:
        visit_module(imp.module_path)

    return ElaborationTypingContext(entries, constructor_to_type, constructor_defs, ctx.instances)


def handle_imports_from_units(
    imports: list[ImportAe],
    defs: list[Definition],
    type_decls: list[TypeDecl],
    compiled_imports: dict,
    _seen_modules: dict[str, QualifiedScope] | None = None,
) -> tuple[list[Definition], list[TypeDecl], list[InductiveDecl], QualifiedScope, UnqualifiedScope]:
    qualified_scope: QualifiedScope = {}
    unqualified_scope: UnqualifiedScope = {}
    imported_inductives: list[InductiveDecl] = []
    seen_modules: dict[str, QualifiedScope] = {} if _seen_modules is None else _seen_modules

    for imp in imports[::-1]:
        if imp.module_path in seen_modules:
            prior_q = seen_modules[imp.module_path]
            for (qual, bare), internal_name in prior_q.items():
                qualified_scope[(qual, bare)] = internal_name
                if imp.is_open or (imp.selected_names and bare in imp.selected_names):
                    unqualified_scope[bare] = internal_name
            continue

        unit = compiled_imports.get(imp.module_path)
        if unit is None:
            continue

        seen_modules[imp.module_path] = {}
        module_name = imp.module_path.split(".")[-1]

        rec_q: QualifiedScope = {}
        rec_u: UnqualifiedScope = {}
        for dep_module in unit.dependencies:
            dep_unit = compiled_imports.get(dep_module)
            if dep_unit is not None:
                dep_name = dep_module.split(".")[-1]
                imported_inductives.extend(dep_unit.inductive_decls)
                type_decls = _merge_type_decls(type_decls, dep_unit.type_decls)
                for (qual, bare), internal_name in dep_unit.qualified_scope.items():
                    rec_q[(qual, bare)] = internal_name
                for bare, export in dep_unit.exports.items():
                    rec_q[(dep_name, bare)] = export.internal_name
            if dep_module in seen_modules:
                rec_q.update(seen_modules[dep_module])

        qualified_scope.update(rec_q)
        unqualified_scope.update(rec_u)
        imported_inductives.extend(unit.inductive_decls)
        type_decls = _merge_type_decls(type_decls, unit.type_decls)

        for (qual, bare), internal_name in unit.qualified_scope.items():
            qualified_scope[(qual, bare)] = internal_name
            seen_modules[imp.module_path][(qual, bare)] = internal_name
            if imp.is_open or (imp.selected_names and bare in imp.selected_names):
                unqualified_scope[bare] = internal_name
            elif not imp.selected_names:
                qualified_scope[(module_name, bare)] = internal_name
                seen_modules[imp.module_path][(module_name, bare)] = internal_name

        for bare, export in unit.exports.items():
            qualified_scope[(module_name, bare)] = export.internal_name
            seen_modules[imp.module_path][(module_name, bare)] = export.internal_name
            if imp.is_open:
                unqualified_scope[bare] = export.internal_name
            elif imp.selected_names and bare in imp.selected_names:
                unqualified_scope[bare] = export.internal_name

    return defs, type_decls, imported_inductives, qualified_scope, unqualified_scope


def _merge_type_decls(existing: list[TypeDecl], new: list[TypeDecl]) -> list[TypeDecl]:
    names = {td.name.name for td in existing}
    merged = list(existing)
    for td in new:
        if td.name.name not in names:
            merged.append(td)
            names.add(td.name.name)
    return merged


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
    program.

    Decorator-generated helper bindings (``@example``/``@property``/fitness
    helpers) are collected and appended *after* all primary definitions rather
    than interleaved right after their owner. Interleaving would split a
    ``mutual`` group — e.g. an ``@example`` on ``even`` inserts a helper between
    ``even`` and ``odd`` — and the evaluator ties a mutual group's recursive knot
    only over the contiguous run of members. Helpers are nullary and only
    *reference* the primary definitions, so placing them last keeps them in scope
    while preserving member contiguity."""
    metadata: Metadata = {}
    primary: list[Definition] = []
    helpers: list[Definition] = []
    for definition in definitions:
        new_def, other_defs, metadata = apply_decorators(definition, metadata)
        primary.append(new_def)
        helpers.extend(other_defs)
    return primary + helpers, metadata


def update_program_and_context(
    prog: STerm,
    defs: list[Definition],
    ctx: ElaborationTypingContext,
) -> tuple[ElaborationTypingContext, STerm]:
    # Pre-compute the signature of every member of each mutual group so each
    # member's SRec can carry its siblings' (name, type) as companions.
    group_members: dict[int, list[tuple[Name, SType]]] = {}
    for d in defs:
        if d.mutual_group_id is not None:
            group_members.setdefault(d.mutual_group_id, []).append((d.name, type_of_definition(d)))

    for d in defs[::-1]:
        match d.body:
            case SVar(Name("uninterpreted", _)):
                ctx.entries.append(ElabUninterpretedBinder(d.name, type_of_definition(d)))
            case _:
                companions: tuple[tuple[Name, SType], ...] = ()
                if d.mutual_group_id is not None:
                    companions = tuple((n, t) for (n, t) in group_members[d.mutual_group_id] if n != d.name)
                prog = convert_definition_to_srec(prog, d, companions=companions)
    return ctx, prog


def _canonicalize_definition_types(defs: list[Definition], type_names: list[Name]) -> list[Definition]:
    canonical: dict[str, Name] = {}
    for name in type_names:
        if name.name not in canonical:
            canonical[name.name] = name

    def canon_ty(ty: SType) -> SType:
        return canonicalize_sconstructor_in_stype(ty, canonical)

    def canon_sterm(t: STerm) -> STerm:

        match t:
            case SApplication(fun, arg, loc):
                return SApplication(canon_sterm(fun), canon_sterm(arg), loc=loc)
            case SAbstraction(name, body, loc):
                return SAbstraction(name, canon_sterm(body), loc=loc)
            case SLet(name, val, body, loc):
                return SLet(name, canon_sterm(val), canon_sterm(body), loc=loc)
            case SIf(cond, then, otherwise, loc):
                return SIf(canon_sterm(cond), canon_sterm(then), canon_sterm(otherwise), loc=loc)
            case SAnnotation(expr, ty, loc):
                return SAnnotation(canon_sterm(expr), canon_ty(ty), loc=loc)
            case SLiteral(v, ty, loc):
                return SLiteral(v, canon_ty(ty), loc=loc)
            case SRec(var_name, ty, val, body, decreasing_by, loc, multiplicity, mutual_group_id, companions):
                return SRec(
                    var_name,
                    canon_ty(ty),
                    canon_sterm(val),
                    canon_sterm(body),
                    decreasing_by=tuple(canon_sterm(m) for m in decreasing_by),
                    loc=loc,
                    multiplicity=multiplicity,
                    mutual_group_id=mutual_group_id,
                    companions=tuple((cn, canon_ty(ct)) for cn, ct in companions),
                )
            case STypeApplication(body, ty, loc):
                return STypeApplication(canon_sterm(body), canon_ty(ty), loc=loc)
            case SMatch(scrutinee, branches, loc):
                return SMatch(
                    canon_sterm(scrutinee),
                    [
                        SMatchBranch(
                            constructor=br.constructor,
                            binders=br.binders,
                            body=canon_sterm(br.body),
                            qualifier=br.qualifier,
                            loc=br.loc,
                        )
                        for br in branches
                    ],
                    loc=loc,
                )
            case _:
                return t

    updated: list[Definition] = []
    for d in defs:
        match d:
            case Definition(name, foralls, args, rtype, body, decorators, rforalls, decreasing_by, loc):
                new_args = [(an, canon_ty(aty)) for an, aty in args]
                updated.append(
                    Definition(
                        name,
                        foralls,
                        new_args,
                        canon_ty(rtype),
                        canon_sterm(body),
                        decorators,
                        rforalls,
                        decreasing_by,
                        loc,
                        arg_multiplicities=d.arg_multiplicities,
                        instance_flags=d.instance_flags,
                    )
                )
    return updated


def canonicalize_imported_type_constructors(
    t: STerm, etctx: ElaborationTypingContext, types: list[Name]
) -> tuple[STerm, ElaborationTypingContext]:
    """Map every ``STypeConstructor`` with a known type name to the canonical ``Name``."""
    canonical: dict[str, Name] = {}
    for name in types:
        if name.name not in canonical:
            canonical[name.name] = name

    def canon_ty(ty: SType) -> SType:
        def rec(inner: SType) -> SType:
            return canonicalize_sconstructor_in_stype(inner, canonical)

        match ty:
            case STypeConstructor(name, args):
                mapped = canonical.get(name.name, name)
                return STypeConstructor(mapped, [rec(a) for a in args])
            case SAbstractionType(var_name, var_type, return_type):
                return SAbstractionType(
                    var_name,
                    rec(var_type),
                    rec(return_type),
                    multiplicity=getattr(ty, "multiplicity", MOmega),
                    is_instance=getattr(ty, "is_instance", False),
                )
            case SRefinedType(binder, base, ref):
                return SRefinedType(binder, rec(base), ref)
            case STypePolymorphism(tname, kind, body):
                return STypePolymorphism(tname, kind, rec(body))
            case SRefinementPolymorphism(rname, sort, body):
                return SRefinementPolymorphism(rname, rec(sort), rec(body))
            case _:
                return ty

    def canon_sterm(node: STerm) -> STerm:
        from aeon.sugar.program import (
            SApplication,
            SIf,
            SLet,
            SLiteral,
            SMatch,
            SMatchBranch,
            SRec,
            STypeApplication,
        )

        match node:
            case SLiteral(v, ty, loc):
                return SLiteral(v, canon_ty(ty), loc=loc)
            case SApplication(fun, arg, loc):
                return SApplication(canon_sterm(fun), canon_sterm(arg), loc=loc)
            case SRec(var_name, ty, val, body, decreasing_by, loc, multiplicity, mutual_group_id, companions):
                return SRec(
                    var_name,
                    canon_ty(ty),
                    canon_sterm(val),
                    canon_sterm(body),
                    decreasing_by=tuple(canon_sterm(m) for m in decreasing_by),
                    loc=loc,
                    multiplicity=multiplicity,
                    mutual_group_id=mutual_group_id,
                    companions=tuple((cn, canon_ty(ct)) for cn, ct in companions),
                )
            case SLet(name, val, body, loc):
                return SLet(name, canon_sterm(val), canon_sterm(body), loc=loc)
            case SIf(cond, then, otherwise, loc):
                return SIf(canon_sterm(cond), canon_sterm(then), canon_sterm(otherwise), loc=loc)
            case STypeApplication(body, ty, loc):
                return STypeApplication(canon_sterm(body), canon_ty(ty), loc=loc)
            case SMatch(scrutinee, branches, loc):
                return SMatch(
                    canon_sterm(scrutinee),
                    [
                        SMatchBranch(
                            constructor=br.constructor,
                            binders=br.binders,
                            body=canon_sterm(br.body),
                            qualifier=br.qualifier,
                            loc=br.loc,
                        )
                        for br in branches
                    ],
                    loc=loc,
                )
            case _ if hasattr(node, "body") and not isinstance(node, SRec):
                return node
            case _:
                return node

    t = canon_sterm(t)

    def fix_entry(e: ElabTypingContextEntry) -> ElabTypingContextEntry:
        match e:
            case ElabVariableBinder(vname, ty):
                return ElabVariableBinder(vname, canon_ty(ty))
            case ElabUninterpretedBinder(vname, ty):
                return ElabUninterpretedBinder(vname, canon_ty(ty))
            case _:
                return e

    etctx = ElaborationTypingContext(
        [fix_entry(e) for e in etctx.entries],
        {k: canonical.get(v.name, v) for k, v in etctx.constructor_to_type.items()},
        etctx.constructor_defs,
    )
    return t, etctx


def canonicalize_sconstructor_in_stype(ty: SType, canonical: dict[str, Name]) -> SType:
    """Canonicalize only the outer constructor name; recurse via caller."""
    match ty:
        case STypeConstructor(name, args):
            mapped = canonical.get(name.name, name)
            return STypeConstructor(
                mapped,
                [canonicalize_sconstructor_in_stype(a, canonical) for a in args],
            )
        case SAbstractionType(var_name, var_type, return_type):
            return SAbstractionType(
                var_name,
                canonicalize_sconstructor_in_stype(var_type, canonical),
                canonicalize_sconstructor_in_stype(return_type, canonical),
                multiplicity=getattr(ty, "multiplicity", MOmega),
                is_instance=getattr(ty, "is_instance", False),
            )
        case SRefinedType(binder, base, ref):
            return SRefinedType(binder, canonicalize_sconstructor_in_stype(base, canonical), ref)
        case STypePolymorphism(tname, kind, body):
            return STypePolymorphism(tname, kind, canonicalize_sconstructor_in_stype(body, canonical))
        case SRefinementPolymorphism(rname, sort, body):
            return SRefinementPolymorphism(
                rname,
                canonicalize_sconstructor_in_stype(sort, canonical),
                canonicalize_sconstructor_in_stype(body, canonical),
            )
        case _:
            return ty


def replace_concrete_types(
    t: STerm, etctx: ElaborationTypingContext, types: list[Name]
) -> tuple[STerm, ElaborationTypingContext]:
    """Replaces all occurrences of STypeVar with the corresponding STypeConstructor."""
    canonical: dict[str, Name] = {}
    for name in types:
        if name.name not in canonical:
            canonical[name.name] = name
    for type_name, name in canonical.items():
        ctor = STypeConstructor(name)
        t = substitution_svartype_in_sterm_by_name(t, ctor, type_name)

    def fix_vartype(e: ElabTypingContextEntry) -> ElabTypingContextEntry:
        match e:
            case ElabVariableBinder(vname, ty):
                nty = ty
                for type_name, name in canonical.items():
                    nty = substitute_svartype_in_stype_by_name(nty, STypeConstructor(name), type_name)
                return ElabVariableBinder(vname, nty)
            case ElabUninterpretedBinder(vname, ty):
                nty = ty
                for type_name, name in canonical.items():
                    nty = substitute_svartype_in_stype_by_name(nty, STypeConstructor(name), type_name)
                return ElabUninterpretedBinder(vname, nty)
            case _:
                return e

    return t, ElaborationTypingContext(
        [fix_vartype(e) for e in etctx.entries], etctx.constructor_to_type, etctx.constructor_defs
    )


def type_of_definition(d: Definition) -> SType:
    match d:
        case Definition(_, foralls, args, rtype, _, _, rforalls, _, loc):
            ntype = rtype
            n_args = len(args)
            for i, (name, atype) in enumerate(reversed(args)):
                idx = n_args - 1 - i
                mult = d.multiplicity_of(idx)
                ntype = SAbstractionType(name, atype, ntype, loc, multiplicity=mult, is_instance=d.is_instance_arg(idx))
            for name, sort in reversed(rforalls):
                ntype = SRefinementPolymorphism(name, sort, ntype, loc)
            for name, kind in reversed(foralls):
                ntype = STypePolymorphism(name, kind, ntype, loc)
            return ntype
        case _:
            assert False, f"{d} is not a definition"


def convert_definition_to_srec(prog: STerm, d: Definition, companions: tuple[tuple[Name, SType], ...] = ()) -> STerm:
    d = definition_with_inferred_decreasing(d)
    match d:
        case Definition(dname, foralls, args, rtype, body, _, rforalls, decreasing_by, loc):
            ntype = rtype
            nbody = body
            n_args = len(args)
            for i, (name, atype) in enumerate(reversed(args)):
                idx = n_args - 1 - i
                mult = d.multiplicity_of(idx)
                ntype = SAbstractionType(
                    name, atype, ntype, loc=loc, multiplicity=mult, is_instance=d.is_instance_arg(idx)
                )
                nbody = SAbstraction(name, nbody, loc=loc)
            for name, sort in reversed(rforalls):
                ntype = SRefinementPolymorphism(name, sort, ntype, loc=loc)
                nbody = SRefinementAbstraction(name, sort, nbody, loc=loc)
            for name, kind in reversed(foralls):
                ntype = STypePolymorphism(name, kind, ntype, loc=loc)
                nbody = STypeAbstraction(name, kind, nbody, loc=loc)
            return SRec(
                dname,
                ntype,
                nbody,
                prog,
                decreasing_by=tuple(decreasing_by),
                loc=loc,
                mutual_group_id=d.mutual_group_id,
                companions=companions,
            )
        case _:
            assert False, f"{d} is not a definition"
