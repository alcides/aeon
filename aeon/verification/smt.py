from __future__ import annotations

import threading
from dataclasses import dataclass
from functools import reduce
from typing import Any
from typing import Generator
from loguru import logger

from z3 import Function
from z3 import Int
from z3 import Length
from z3 import IntVal
from z3 import Real
from z3 import RealVal
from z3 import Solver
from z3 import StringVal
from z3 import sat
from z3 import unknown
from z3.z3 import And
from z3.z3 import Bool
from z3.z3 import BoolRef
from z3.z3 import BoolSort
from z3.z3 import Const
from z3.z3 import DeclareSort
from z3.z3 import If
from z3.z3 import Implies
from z3.z3 import IntSort
from z3.z3 import RealSort
from z3.z3 import Not
from z3.z3 import Or
from z3.z3 import String
from z3.z3 import StringSort
from z3.z3 import SortRef
from z3.z3types import Z3Exception
from z3 import Datatype
from z3 import Context, main_ctx
from z3 import ArraySort
from z3 import BoolVal
from z3 import Distinct, EmptySet, SetAdd, SetUnion, SetIntersect, SetDifference, IsMember, IsSubset

from aeon.core.liquid import LiquidApp
from aeon.core.types import LiquidHornApplication, TypeConstructor
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralFloat
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidLiteralUnit
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.liquid import liquid_free_vars
from aeon.core.liquid_ops import mk_liquid_and
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType, RefinedType, RefinementPolymorphism, Top, TypePolymorphism
from aeon.core.types import Type
from aeon.core.types import TypeVar
from aeon.core.types import t_bool, t_int, t_float, t_set, t_string, t_unit
from aeon.verification.sub import lower_constraint_type
from aeon.verification.vcs import Conjunction
from aeon.verification.vcs import alpha_key
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import Implication
from aeon.verification.vcs import LiquidConstraint
from aeon.verification.vcs import ReflectedFunctionDeclaration
from aeon.verification.vcs import UninterpretedFunctionDeclaration
from aeon.utils.name import Name, fresh_counter


def _set_sort(ctx) -> SortRef:
    """Set-of-Int sort in ``ctx``. z3py's ``SetSort`` hardcodes a default-context
    ``BoolSort()`` for the array range, so it raises "Context mismatch" on a
    worker context -- build the array sort explicitly instead."""
    return ArraySort(IntSort(ctx), BoolSort(ctx))


smt_function_types: dict[str, list[Type]] = {
    "smtEqInt": [t_int, t_int, t_bool],
    "smtEqFloat": [t_float, t_float, t_bool],
    "smtEqBool": [t_float, t_float, t_bool],
    "smtEqString": [t_string, t_string, t_bool],
    "smtNeqInt": [t_int, t_int, t_bool],
    "smtNeqFloat": [t_float, t_float, t_bool],
    "smtNeqBool": [t_float, t_float, t_bool],
    "smtNeqString": [t_string, t_string, t_bool],
    "smtNot": [t_bool, t_bool],
    "smtLeqInt": [t_int, t_int, t_bool],
    "smtLeqFloat": [t_float, t_float, t_bool],
    "smtLtInt": [t_int, t_int, t_bool],
    "smtLtFloat": [t_float, t_float, t_bool],
    "smtAnd": [t_bool, t_bool, t_bool],
    "smtOr": [t_bool, t_bool, t_bool],
    "smtPlusInt": [t_int, t_int, t_int],
    "smtMinusInt": [t_int, t_int, t_int],
    "smtMultInt": [t_int, t_int, t_int],
    "smtDivInt": [t_int, t_int, t_int],
    "smtModInt": [t_int, t_int, t_int],
    "smtPlusFloat": [t_float, t_float, t_float],
    "smtMinusFloat": [t_float, t_float, t_float],
    "smtMultFloat": [t_float, t_float, t_float],
    "smtDivFloat": [t_float, t_float, t_float],
    "smtImplies": [t_bool, t_bool, t_bool],
    # SMT Set operations
    "smtSetSng": [t_int, t_set],
    "smtSetCup": [t_set, t_set, t_set],
    "smtSetCap": [t_set, t_set, t_set],
    "smtSetDif": [t_set, t_set, t_set],
    "smtSetMem": [t_int, t_set, t_bool],
    "smtSetSub": [t_set, t_set, t_bool],
    "smtEqSet": [t_set, t_set, t_bool],
    "smtNeqSet": [t_set, t_set, t_bool],
}

smt_function_translation: dict[str, list[str]] = {
    "==": ["smtEqBool", "smtEqInt", "smtEqFloat", "smtEqString", "smtEqSet"],
    "!=": ["smtNeqBool", "smtNeqInt", "smtNeqFloat", "smtNeqString", "smtNeqSet"],
    "!": ["smtNot"],
    "<": ["smtLeqInt", "smtLeqFloat"],
    "<=": ["smtLtInt", "smtLtFloat"],
    "&&": ["smtAnd"],
    "||": ["smtOr"],
    "+": ["smtPlusInt", "smtPlusFloat"],
    "-": ["smtMinusInt", "smtMinusFloat"],
    "*": ["smtMultInt", "smtMultFloat"],
    "/": ["smtDivInt", "smtDivFloat"],
    "%": ["smtModInt"],
    "-->": ["smtImplies"],
    "Set_sng": ["smtSetSng"],
    "Set_cup": ["smtSetCup"],
    "Set_cap": ["smtSetCap"],
    "Set_dif": ["smtSetDif"],
    "Set_mem": ["smtSetMem"],
    "Set_sub": ["smtSetSub"],
}


def _build_base_functions(ctx) -> dict[str, Any]:
    """Build the SMT operator table bound to a specific Z3 context.

    Most entries are lambdas whose Z3 context is inferred from their operands,
    but ``Set_empty``/``Set_sng`` mint a root ``EmptySet(IntSort())`` that must
    live in ``ctx`` -- so the table is per-context (one per worker thread)."""
    empty = EmptySet(IntSort(ctx))
    return {
        "==": lambda x, y: x == y,
        "!=": lambda x, y: x != y,
        "<": lambda x, y: x < y,
        "<=": lambda x, y: x <= y,
        ">": lambda x, y: x > y,
        ">=": lambda x, y: x >= y,
        "!": lambda x: Not(x),
        "&&": lambda x, y: And(x, y),
        "||": lambda x, y: Or(x, y),
        "+": lambda x, y: x + y,
        "-": lambda x, y: x - y,
        "*": lambda x, y: x * y,
        "/": lambda x, y: x / y,
        "%": lambda x, y: x % y,
        "-->": lambda x, y: Implies(x, y),
        "ite": lambda c, t, e: If(c, t, e),
        # String.len -> Z3's native string-length, so refinements over string length
        # (e.g. the `len i` preconditions of String.slice/replace/split) connect to
        # Z3's string theory. Without this, `String_len` would be an uninterpreted
        # symbol and `len "hello"` could not be shown to equal 5, so length-refined
        # operations were undischargeable on string literals.
        "String_len": lambda s: Length(s),
        # SMT Set operations
        "Set_empty": empty,
        "Set_sng": lambda x: SetAdd(empty, x),
        "Set_cup": lambda a, b: SetUnion(a, b),
        "Set_cap": lambda a, b: SetIntersect(a, b),
        "Set_dif": lambda a, b: SetDifference(a, b),
        "Set_mem": lambda x, s: IsMember(x, s),
        "Set_sub": lambda a, b: IsSubset(a, b),
    }


# The default-context operator table, for external importers
# (``aeon.synthesis.modules.*``) and the main thread's state.
base_functions: dict[str, Any] = _build_base_functions(main_ctx())


@dataclass
class SMTContext:
    sorts: list[str]
    functions: dict[str, AbstractionType]
    variables: dict[str, TypeConstructor]
    premises: list[LiquidTerm]
    reflected_functions: dict[str, tuple[tuple[Name, ...], LiquidTerm]]

    def with_sort(self, name: Name) -> SMTContext:
        return SMTContext(
            self.sorts + [str(name)], self.functions, self.variables, self.premises, self.reflected_functions
        )

    def with_function(self, name: Name, ty: AbstractionType) -> SMTContext:
        return SMTContext(
            self.sorts, {**self.functions, str(name): ty}, self.variables, self.premises, self.reflected_functions
        )

    def with_var(self, name: Name, ty: TypeConstructor) -> SMTContext:
        return SMTContext(
            self.sorts, self.functions, {**self.variables, str(name): ty}, self.premises, self.reflected_functions
        )

    def with_premise(self, p: LiquidTerm) -> SMTContext:
        return SMTContext(self.sorts, self.functions, self.variables, self.premises + [p], self.reflected_functions)

    def with_reflected_function(self, name: Name, params: tuple[Name, ...], body: LiquidTerm) -> SMTContext:
        return SMTContext(
            self.sorts,
            self.functions,
            self.variables,
            self.premises,
            {**self.reflected_functions, str(name): (params, body)},
        )


def _ple_unfold_once(
    t: LiquidTerm,
    reflected_functions: dict[str, tuple[tuple[Name, ...], LiquidTerm]],
) -> tuple[LiquidTerm, bool]:
    match t:
        case LiquidApp(fun, args, loc):
            n_args: list[LiquidTerm] = []
            changed = False
            for arg in args:
                n_arg, arg_changed = _ple_unfold_once(arg, reflected_functions)
                n_args.append(n_arg)
                changed = changed or arg_changed
            key = str(fun)
            if key in reflected_functions:
                params, body = reflected_functions[key]
                if len(params) == len(n_args):
                    unfolded = body
                    for param, arg in zip(params, n_args):
                        unfolded = substitution_in_liquid(unfolded, arg, param)
                    return unfolded, True
            if changed:
                return LiquidApp(fun, n_args, loc=loc), True
            return t, False
        case _:
            return t, False


# Cache for ``ple_unfold_fixpoint`` keyed by ``(id(term), id(reflected_funcs))``
# with identity checks (so a recycled ``id`` can never yield a stale hit). With
# premise objects shared across the conjuncts of a solve (see
# ``_specialize_liquid_term``), the same unfolding is requested repeatedly;
# unfolding is a pure function of its inputs, so reusing the result is sound.
_ple_cache: dict[tuple[int, int], tuple[LiquidTerm, dict, LiquidTerm]] = {}


def ple_unfold_fixpoint(
    t: LiquidTerm,
    reflected_functions: dict[str, tuple[tuple[Name, ...], LiquidTerm]],
    max_steps: int = 256,
) -> LiquidTerm:
    # No reflected functions in scope -> nothing can unfold. Skip the loop
    # (and its per-call ``repr``/``term_size`` work, which otherwise dominates
    # on large reflection-free premises) and return the term unchanged. This
    # also preserves object identity, which the translate-time memo relies on.
    if not reflected_functions:
        return t
    cache = _ws().ple  # per-thread: pure term rewriting, but a shared dict would race
    key = (id(t), id(reflected_functions))
    hit = cache.get(key)
    if hit is not None and hit[0] is t and hit[1] is reflected_functions:
        return hit[2]
    result = _ple_unfold_fixpoint_uncached(t, reflected_functions, max_steps)
    cache[key] = (t, reflected_functions, result)
    _bound(cache)
    return result


def _ple_unfold_fixpoint_uncached(
    t: LiquidTerm,
    reflected_functions: dict[str, tuple[tuple[Name, ...], LiquidTerm]],
    max_steps: int = 256,
) -> LiquidTerm:
    def term_size(node: LiquidTerm) -> int:
        match node:
            case LiquidApp(_, args):
                return 1 + sum(term_size(a) for a in args)
            case _:
                return 1

    max_term_size = 4096
    current = t
    start_size = term_size(current)
    seen: set[str] = {repr(current)}
    unfolded_steps = 0
    stop_reason = "fixpoint"
    for _ in range(max_steps):
        current, changed = _ple_unfold_once(current, reflected_functions)
        if not changed:
            stop_reason = "no_change"
            break
        unfolded_steps += 1
        if term_size(current) > max_term_size:
            stop_reason = "size_guard"
            break
        signature = repr(current)
        if signature in seen:
            stop_reason = "seen_guard"
            break
        seen.add(signature)
    logger.debug(
        "PLE unfold: steps={} start_size={} final_size={} stop={} reflected_funs={}",
        unfolded_steps,
        start_size,
        term_size(current),
        stop_reason,
        len(reflected_functions),
    )
    return current


def _name_token(name: Name) -> str:
    """Mangling token for a ``Name``.

    Includes the binder ID (separated by ``__`` so it can't be confused
    with the single-``_`` separator between mangled args) when non-zero
    — so two user types that share a string name but live in different
    scopes (e.g. ``T`` imported from two modules) don't accidentally
    collide on a single Z3 sort.
    """
    if name.id <= 0:
        return name.name
    return f"{name.name}__{name.id}"


def _mangle_sort_name(t: Type) -> str:
    """Deterministic sort name for a parametric type constructor.

    ``Pair Dataset Dataset`` → ``"Pair_Dataset_Dataset"`` (with
    per-``Name`` ID suffixes appended via ``__id`` when the binder ID
    is non-zero); nested apps mangle recursively. Used by ``get_sort``
    to give each instantiation its own Z3 sort while keeping the sort
    name consistent across uses (so two variables of the same Aeon
    type share a Z3 sort and can be compared).
    """
    match t:
        case TypeConstructor(name, []):
            return _name_token(name)
        case TypeConstructor(name, args):
            return _name_token(name) + "_" + "_".join(_mangle_sort_name(a) for a in args)
        case TypeVar(name):
            return _name_token(name)
        case _:
            return str(t)


def _specialize_type(ty: Type, mapping: dict[str, TypeConstructor]) -> Type:
    match ty:
        case TypeConstructor(name, args) if not args:
            return mapping.get(name.name, ty)
        case TypeConstructor(name, args):
            # Recurse into args: ``Pair a b`` with mapping ``{a → Dataset,
            # b → Dataset}`` becomes ``Pair Dataset Dataset``.
            sargs = [_specialize_type(a, mapping) for a in args]
            assert all(isinstance(s, (TypeConstructor, TypeVar, RefinedType)) for s in sargs)
            return TypeConstructor(name, sargs, loc=ty.loc)
        case AbstractionType(vname, vty, body, loc):
            svty = _specialize_type(vty, mapping)
            sbody = _specialize_type(body, mapping)
            assert isinstance(svty, (Top, TypeVar, TypeConstructor, RefinedType, AbstractionType))
            return AbstractionType(vname, svty, sbody, loc=loc)
        case TypePolymorphism(_, _, body):
            return _specialize_type(body, mapping)
        case RefinementPolymorphism(_, _, body):
            return _specialize_type(body, mapping)
        case RefinedType(vname, bty, ref, loc):
            sbty = _specialize_type(bty, mapping)
            assert isinstance(sbty, (TypeConstructor, TypeVar))
            return RefinedType(vname, sbty, ref, loc=loc)
        case _:
            return ty


def _collect_specialisation(expected: Type, actual: Type, subst: dict[str, TypeConstructor]) -> None:
    """Walk an expected/actual type pair to harvest TypeVar bindings.

    For a polymorphic projection whose param type is ``Pair a b`` and a
    call-site whose argument has type ``Pair Dataset Dataset``, populate
    ``subst`` with ``a → Dataset`` and ``b → Dataset``. Only fires when
    the *expected* position is a TypeConstructor with a lowercase name
    (the convention for lowered TypeVars).

    ``actual`` originates from ``_term_base_type``, which only ever
    returns a ``TypeConstructor`` (or ``None``, which the caller
    filters before invoking us). Inner recursive calls also stay within
    the TypeConstructor world because we descend into ``actual.args``.
    Nothing else makes sense as a Z3-typeable carrier of a substitution.
    """
    assert isinstance(actual, TypeConstructor), (
        f"_collect_specialisation: actual must be a TypeConstructor (got {actual!r}); "
        f"_term_base_type is the documented source and only returns TypeConstructor"
    )
    if not isinstance(expected, TypeConstructor):
        return
    if not expected.args:
        n = expected.name.name
        if n[:1].islower() and n not in {"Int", "Bool", "Float", "String", "Unit", "Top"}:
            subst[n] = actual
        return
    if expected.name == actual.name and len(expected.args) == len(actual.args):
        for ea, aa in zip(expected.args, actual.args):
            _collect_specialisation(ea, aa, subst)


def _term_base_type(
    t: LiquidTerm,
    variables: dict[str, TypeConstructor],
    functions: dict[str, AbstractionType] | None = None,
) -> TypeConstructor | None:
    match t:
        case LiquidLiteralInt():
            return t_int
        case LiquidLiteralFloat():
            return t_float
        case LiquidLiteralBool():
            return t_bool
        case LiquidLiteralString():
            return t_string
        case LiquidLiteralUnit():
            return t_unit
        case LiquidVar(name):
            return variables.get(str(name), None)
        case LiquidApp(fun_name, args) if functions is not None:
            # A fully-applied function/constructor argument (e.g. a
            # ``.box 3`` constructor or a recursively-resolved instance
            # dictionary). Its base type is the function's result type
            # after peeling one abstraction per supplied argument. By the
            # time we get here ``_specialize_liquid_term`` has already
            # processed the argument subterm, so a monomorphised twin with
            # a concrete result type is in ``functions``.
            fty = functions.get(str(fun_name))
            if fty is None:
                return None
            cur: Type = fty
            while isinstance(cur, (TypePolymorphism, RefinementPolymorphism)):
                cur = cur.body
            for _ in args:
                if not isinstance(cur, AbstractionType):
                    return None
                cur = cur.type
            lowered = lower_constraint_type(cur)
            return lowered if isinstance(lowered, TypeConstructor) else None
        case _:
            return None


def _specialization_name(base: str, concrete: tuple[str, ...]) -> str:
    return f"{base}__spec__{'__'.join(concrete)}"


def _specialize_liquid_term(
    t: LiquidTerm,
    functions: dict[str, AbstractionType],
    variables: dict[str, TypeConstructor],
    reflected_functions: dict[str, tuple[tuple[Name, ...], LiquidTerm]],
    specializations: dict[tuple[str, tuple[str, ...]], str],
) -> tuple[LiquidTerm, dict[str, AbstractionType], dict[str, tuple[tuple[Name, ...], LiquidTerm]]]:
    if not isinstance(t, LiquidApp):
        return t, functions, reflected_functions

    nfuncs = functions
    nref = reflected_functions
    nargs: list[LiquidTerm] = []
    # Track whether any argument was actually rewritten. When nothing changes
    # we return the *original* ``t`` object rather than an identical-but-fresh
    # ``LiquidApp``. `flatten` specializes the same accumulated-premise objects
    # once per sibling conjunct, so preserving identity here lets the
    # translate-time memo (keyed by object id) dedup those premises across the
    # many CanonicConstraints of one solve instead of re-walking them each time.
    args_changed = False
    for a in t.args:
        sa, nfuncs, nref = _specialize_liquid_term(a, nfuncs, variables, nref, specializations)
        if sa is not a:
            args_changed = True
        nargs.append(sa)

    fname = str(t.fun)
    if fname not in nfuncs:
        return (t if not args_changed else LiquidApp(t.fun, nargs, loc=t.loc)), nfuncs, nref

    fty = nfuncs[fname]
    cur: Type = fty
    subst: dict[str, TypeConstructor] = {}
    for arg in nargs:
        if not isinstance(cur, AbstractionType):
            break
        actual = _term_base_type(arg, variables, nfuncs)
        if actual is not None:
            _collect_specialisation(cur.var_type, actual, subst)
        cur = cur.type

    if not subst:
        return (t if not args_changed else LiquidApp(t.fun, nargs, loc=t.loc)), nfuncs, nref

    concrete_sig = tuple(sorted(_mangle_sort_name(v) for v in subst.values()))
    skey = (fname, concrete_sig)
    if skey in specializations:
        sname = specializations[skey]
    else:
        sname = _specialization_name(fname, concrete_sig)
        nty = _specialize_type(fty, subst)
        assert isinstance(nty, AbstractionType)
        nfuncs = {**nfuncs, sname: nty}
        if fname in nref:
            nref = {**nref, sname: nref[fname]}
        specializations[skey] = sname
    return LiquidApp(Name(sname, 0), nargs, loc=t.loc), nfuncs, nref


def _ctx_with_curried_formals(ctx: SMTContext, fun_ty: AbstractionType) -> SMTContext:
    """Add Z3-scalar bindings for each curried parameter of ``fun_ty`` (for UFD / recursion VCs)."""
    out = ctx
    cur: Type = fun_ty
    while isinstance(cur, AbstractionType):
        base = lower_constraint_type(cur.var_type)
        base_tc: TypeConstructor
        match base:
            case TypeVar(iname):
                base_tc = TypeConstructor(iname)
            case TypeConstructor(_, _):
                # Keep args; ``get_sort`` mangles to a per-instantiation
                # Z3 sort so distinct instantiations stay separable while
                # still being shared across uses of the same Aeon type.
                base_tc = base
            case AbstractionType(_, _, _) | TypePolymorphism(_, _, _) | RefinementPolymorphism(_, _, _):
                base_tc = t_int
            case _:
                assert False, f"{base} ({type(base)}) is not a base type for curried formal."
        out = out.with_var(cur.var_name, base_tc)
        cur = cur.type
    return out


@dataclass(init=False)
class CanonicConstraint:
    """Represents SMT-valid constraints."""

    sorts: list[str]
    functions: dict[str, AbstractionType]
    variables: dict[str, TypeConstructor]
    premise: LiquidTerm
    conclusion: LiquidTerm

    def __init__(self, ctx: SMTContext, pos: LiquidTerm):
        self.sorts = ctx.sorts
        self.functions = ctx.functions
        self.variables = ctx.variables
        self.premise = reduce(mk_liquid_and, ctx.premises, LiquidLiteralBool(True))
        self.conclusion = pos


def rename_constraint(c: Constraint, old_name: Name, new_name: Name) -> Constraint:
    """Renames a binder within the constraint, to make it is unique."""
    match c:
        case LiquidConstraint(expr):
            nexpr = substitution_in_liquid(expr, LiquidVar(new_name), old_name)
            return LiquidConstraint(expr=nexpr)
        case Conjunction(c1, c2):
            return Conjunction(rename_constraint(c1, old_name, new_name), rename_constraint(c2, old_name, new_name))
        case Implication(name, base, pred, seq):
            if name == new_name:
                return c
            else:
                npred = substitution_in_liquid(pred, LiquidVar(new_name), old_name)
                nseq = rename_constraint(seq, old_name, new_name)
                return Implication(name, base, npred, nseq)
        case UninterpretedFunctionDeclaration(name, absty, seq):
            nseq = rename_constraint(seq, old_name, new_name)
            return UninterpretedFunctionDeclaration(name, absty, nseq)
        case ReflectedFunctionDeclaration(name, absty, params, body, seq):
            nbody = substitution_in_liquid(body, LiquidVar(new_name), old_name)
            nparams = tuple(new_name if p == old_name else p for p in params)
            nseq = rename_constraint(seq, old_name, new_name)
            return ReflectedFunctionDeclaration(name, absty, nparams, nbody, nseq)
        case _:
            assert False, f"Unexpected case {c} ({type(c)})"


_RENAME_ABSENT = object()


def _rename_vars(t: LiquidTerm, renames: dict[Name, Name]) -> LiquidTerm:
    """Apply a batch of binder renamings (old ``Name`` -> fresh ``Name``) in a
    single pass over ``t``.

    Equivalent to composing ``substitution_in_liquid(t, LiquidVar(new), old)``
    for every ``old -> new`` pair, but in one traversal. The composition order is
    irrelevant because every ``new`` is globally fresh (``fresh_counter``), so no
    rename target collides with another rename's source. Returns ``t`` unchanged
    when ``renames`` is empty (the common leaf case)."""
    if not renames:
        return t
    match t:
        case LiquidVar(name):
            new = renames.get(name)
            return LiquidVar(new) if new is not None else t
        case LiquidApp(fun, args, loc):
            return LiquidApp(renames.get(fun, fun), [_rename_vars(a, renames) for a in args], loc=loc)
        case LiquidHornApplication(name, argtypes, loc):
            # Mirrors ``substitution_in_liquid``: the head name is passed through,
            # only argument terms are rewritten.
            return LiquidHornApplication(name, [(_rename_vars(a, renames), ty) for (a, ty) in argtypes], loc=loc)
        case _:
            return t


def _conjuncts(t: LiquidTerm) -> list[LiquidTerm]:
    """Split a liquid term into its top-level ``&&`` conjuncts."""
    if isinstance(t, LiquidApp) and t.fun.name == "&&" and len(t.args) == 2:
        return _conjuncts(t.args[0]) + _conjuncts(t.args[1])
    return [t]


def _var_equality(p: LiquidTerm, variables: dict[str, Any], eliminated: set[str]) -> tuple[Name, LiquidTerm] | None:
    """If ``p`` is ``x == Y`` (or ``Y == x``) with ``x`` an as-yet-uneliminated
    scalar binder, return ``(x, Y)`` -- the variable to remove and its definition."""
    if isinstance(p, LiquidApp) and p.fun.name == "==" and len(p.args) == 2:
        a, b = p.args
        if isinstance(a, LiquidVar) and str(a.name) in variables and str(a.name) not in eliminated:
            return a.name, b
        if isinstance(b, LiquidVar) and str(b.name) in variables and str(b.name) not in eliminated:
            return b.name, a
    return None


def _symbols(t: LiquidTerm) -> set[str]:
    """Variable *and* function symbols occurring in ``t`` (``liquid_free_vars``
    includes ``LiquidApp`` heads, so reflected measures/constructors count)."""
    return {str(n) for n in liquid_free_vars(t)}


def _simplify_vc(
    premises: list[LiquidTerm],
    conclusion: LiquidTerm,
    variables: dict[str, Any],
    functions: dict[str, Any],
) -> tuple[list[LiquidTerm], LiquidTerm, dict[str, Any], dict[str, Any]]:
    """Shrink an obligation before it is handed to Z3.

    1. flatten ``&&`` and drop trivially-true conjuncts (``True && P == P``);
    2. equality elimination -- *exact*: a premise ``x == Y`` with ``x`` a
       universally quantified binder and ``Y`` free of ``x`` pins ``x`` to ``Y``,
       so substitute ``x := Y`` everywhere and drop both. Collapses the ANF
       ``h_i == e_i`` chains that bloat these VCs;
    3. relevance slicing -- keep only premises/variables/functions transitively
       connected (through shared symbols) to the conclusion. Dropping a premise
       only weakens the hypothesis, so this never makes an invalid program look
       valid (sound). It is exact whenever the dropped premises are satisfiable
       -- the sole incompleteness is a disconnected *inconsistent* premise that
       would vacuously discharge the goal (e.g. dead-code refinement contexts).
       This is what removes the irrelevant ``open``-library function declarations
       (supermario's ``gpu_dot`` &c.) that equality elimination cannot touch.
    """
    flat: list[LiquidTerm] = []
    for p in premises:
        flat.extend(_conjuncts(p))
    flat = [p for p in flat if not (isinstance(p, LiquidLiteralBool) and p.value is True)]

    # 2. equality elimination
    eliminated: set[str] = set()
    changed = True
    while changed:
        changed = False
        for i, p in enumerate(flat):
            found = _var_equality(p, variables, eliminated)
            if found is None:
                continue
            x, y = found
            if x in liquid_free_vars(y):  # occurs check: can't eliminate x == f(x)
                continue
            rest = flat[:i] + flat[i + 1 :]
            flat = [substitution_in_liquid(q, y, x) for q in rest]
            conclusion = substitution_in_liquid(conclusion, y, x)
            eliminated.add(str(x))
            changed = True
            break
    if eliminated:
        variables = {k: v for k, v in variables.items() if k not in eliminated}

    # 3. relevance slicing: transitive cone of influence from the conclusion
    relevant = _symbols(conclusion)
    changed = True
    while changed:
        changed = False
        for p in flat:
            ps = _symbols(p)
            if ps & relevant and not ps <= relevant:
                relevant |= ps
                changed = True
    # keep premises sharing a symbol with the goal's cone (ground premises -- no
    # symbols at all -- are kept: they are cheap and may be contradictory).
    flat = [p for p in flat if (not _symbols(p)) or (_symbols(p) & relevant)]
    variables = {k: v for k, v in variables.items() if k in relevant}
    functions = {k: v for k, v in functions.items() if k in relevant}
    return flat, conclusion, variables, functions


def flatten(
    c: Constraint,
    ctx: SMTContext | None = None,
    renames: dict[Name, Name] | None = None,
) -> Generator[CanonicConstraint]:
    """Flattens a constraint into a list of SMT-valid constraints.

    Binders are alpha-renamed to globally fresh names (so each name has a single
    sort throughout a solve). Rather than eagerly rebuilding the whole remaining
    constraint at every ``forall`` binder -- which is O(depth^2) substitution and
    made ``substitution_in_liquid`` the hottest function in the system -- the
    renamings are accumulated in ``renames`` and applied in a single pass to each
    premise/conclusion as it is consumed. Each subterm is walked once, so the
    pass is linear in the constraint size."""
    if ctx is None:
        ctx = SMTContext(["Top"], {}, {}, [], {})
    if renames is None:
        renames = {}
    match c:
        case LiquidConstraint(expr):
            # Premises were renamed as they were pushed onto ``ctx`` (below); the
            # conclusion still carries original names, so rename it here.
            expr = _rename_vars(expr, renames)
            specializations: dict[tuple[str, tuple[str, ...]], str] = {}
            nfunctions = ctx.functions
            nref = ctx.reflected_functions
            sprem: list[LiquidTerm] = []
            for p in ctx.premises:
                sp, nfunctions, nref = _specialize_liquid_term(p, nfunctions, ctx.variables, nref, specializations)
                sprem.append(sp)
            sexpr, nfunctions, nref = _specialize_liquid_term(expr, nfunctions, ctx.variables, nref, specializations)
            premise = [ple_unfold_fixpoint(p, nref) for p in sprem]
            conclusion = ple_unfold_fixpoint(sexpr, nref)
            premise, conclusion, svariables, sfunctions = _simplify_vc(premise, conclusion, ctx.variables, nfunctions)
            out_ctx = SMTContext(ctx.sorts, sfunctions, svariables, premise, nref)
            yield CanonicConstraint(out_ctx, conclusion)
        case Conjunction(c1, c2):
            yield from flatten(c1, ctx, renames)
            yield from flatten(c2, ctx, renames)
        case Implication(oname, base, pred, seq):
            name = Name(oname.name, fresh_counter.fresh())
            # ``pred`` is in scope of this binder and all ancestors: apply the
            # full accumulated map (incl. this binder) once, and store the
            # already-renamed premise on the context.
            prev = renames.get(oname, _RENAME_ABSENT)
            renames[oname] = name
            npred = _rename_vars(pred, renames)
            match base:
                case TypeVar(iname):
                    base = TypeConstructor(iname)
                case TypeConstructor(_, _):
                    # Keep args; ``get_sort`` mangles to a per-instantiation
                    # Z3 sort while leaving the Aeon-level type intact so
                    # ``_specialize_liquid_term`` can read its shape.
                    pass
                case _:
                    assert False, f"{base} ({type(base)}) is not a base type."
            yield from flatten(seq, ctx.with_var(name, base).with_premise(npred), renames)
            # Restore so sibling scopes (e.g. the other arm of a Conjunction) do
            # not see this binder. Safe with the generator: each yielded
            # CanonicConstraint is already concrete and holds no reference to
            # ``renames``.
            if prev is _RENAME_ABSENT:
                del renames[oname]
            else:
                renames[oname] = prev  # type: ignore[assignment]
        case UninterpretedFunctionDeclaration(name, ty, seq):
            assert isinstance(c, UninterpretedFunctionDeclaration)
            nctx = _ctx_with_curried_formals(ctx, ty)
            yield from flatten(seq, nctx.with_function(name, ty), renames)
        case ReflectedFunctionDeclaration(name, ty, params, body, seq):
            # The reflected body and params are in scope of the ancestor binders;
            # apply the accumulated renames before building the equality premise.
            nparams = tuple(renames.get(p, p) for p in params)
            nbody = _rename_vars(body, renames)
            nctx = (
                _ctx_with_curried_formals(ctx, ty).with_function(name, ty).with_reflected_function(name, nparams, nbody)
            )
            app = LiquidApp(name, [LiquidVar(p) for p in nparams])
            eq = LiquidApp(Name("==", 0), [app, nbody])
            yield from flatten(seq, nctx.with_premise(eq), renames)
        case _:
            assert False, f"Cannot flatten {c}."


# Main-thread Z3 solver (default context). Workers get their own via ``_ws()``.
s = Solver(ctx=main_ctx())
s.set(timeout=200)

# Validity results are context-independent (keyed by the alpha-normalized
# constraint string), so this stays a single shared cache across threads, guarded
# by a lock -- a constraint proved by any thread is reused by all.
_smt_valid_cache: dict[str, bool] = {}
_cache_lock = threading.Lock()


class _WS:
    """Per-thread Z3 state. Z3 is not thread-safe across a shared ``Context``, so
    each worker thread that validates concurrently gets its own ``Context``,
    ``Solver``, operator table and object caches. The main thread reuses the
    module-global (default-context) objects, so external importers of
    ``base_functions`` / ``make_variable`` are unaffected."""

    ctx: Any
    solver: Any
    sort_cache: dict[str, Any]
    base_functions: dict[str, Any]
    unit_sort: Any
    unit_value: Any
    mk_vars: dict[int, Any]
    mk_funs: dict[int, Any]
    mk_sorts: dict[tuple[str, ...], Any]
    ple: dict[Any, Any]


def _new_ws(ctx) -> "_WS":
    w = _WS()
    w.ctx = ctx
    w.solver = Solver(ctx=ctx)
    w.solver.set(timeout=200)
    w.unit_sort, w.unit_value = _build_unit_sort(ctx)
    w.sort_cache = {"Unit": w.unit_sort}
    w.base_functions = _build_base_functions(ctx)
    w.mk_vars, w.mk_funs, w.mk_sorts, w.ple = {}, {}, {}, {}
    return w


_local = threading.local()


def _ws() -> "_WS":
    w = getattr(_local, "w", None)
    if w is None:
        # Main thread reuses the default-context module globals (behaviour
        # identical to before the refactor); workers get a private context.
        w = _MAIN if threading.current_thread() is threading.main_thread() else _new_ws(Context())
        _local.w = w
    return w


def smt_valid(constraint: Constraint) -> bool:
    """Verifies if a constraint is true using Z3."""
    key = alpha_key(constraint)
    with _cache_lock:
        cached = _smt_valid_cache.get(key)
    if cached is not None:
        return cached

    ws = _ws()
    solver = ws.solver

    def _memo(result: bool) -> bool:
        with _cache_lock:
            _smt_valid_cache[key] = result
        return result

    # One memo per solve: the constraints produced by `flatten` share their
    # accumulated premise subterms (same objects), so translating them once and
    # reusing the Z3 ASTs across conjuncts removes the dominant re-translation
    # cost. Scoped here (not module-global) so it never spans solves with
    # different alpha-renamed namespaces, and discarded when this call returns.
    translate_memo: dict[int, tuple[LiquidTerm, Any]] = {}
    n = 0
    for c in flatten(constraint):
        n += 1
        solver.push()

        # Monomorphic, uncurried function declarations need no separate
        # emission step here: each CanonicConstraint carries its own
        # `functions` (including the monomorphised twins minted by
        # `_specialize_liquid_term`), and `translate` -> `mk_funs` uncurries
        # them into Z3 `Function`s while building this constraint's formula.
        # Z3 declares a function symbol implicitly wherever it appears in the
        # asserted formula, and the push/pop here scopes each constraint, so
        # the declarations are re-emitted per constraint by construction.
        try:
            try:
                smt_c = translate(c, translate_memo)
            except ZeroDivisionError:
                # A constant division/modulo by zero (e.g. ``-2 / 0``) is
                # undefined: it crashes at runtime and Z3 leaves it
                # unconstrained. *Skipping* the obligation silently *assumed* it
                # valid -- unsound, and it let absurd refinements through (any
                # spec was "satisfied" by a literal ``/ 0``). An obligation we
                # cannot even define is not proven, so report it invalid.
                return _memo(False)
            if smt_c is False:
                continue
            solver.add(smt_c)
            result = solver.check()
            if result == sat:
                return _memo(False)
            elif result == unknown:
                return _memo(False)
        finally:
            # Always balance the matching ``push`` -- the solver is reused across
            # this thread's queries, so an early ``return``/``continue`` that
            # skipped the pop would leak scope state into later ones.
            solver.pop()

    return _memo(True)


def type_of_variable(variables: list[tuple[str, Any]], name: str) -> Any:
    for na, ref in reversed(variables):
        if na == name:
            return ref
    vars = ", ".join([x[0] for x in variables])
    logger.error(f"No variable {name} in the context: {vars}")
    assert False


sort_cache: dict[str, SortRef] = {}


def _build_unit_sort(ctx) -> tuple[SortRef, Any]:
    """Create the dedicated Unit sort and its single inhabitant, in ``ctx``.

    Modelled as a z3 datatype with one nullary constructor so the SMT
    solver knows the sort has exactly one value. This avoids the previous
    encoding that aliased ``Unit`` to ``Bool``-true (see issue #296), under
    which ``unit == True`` was accidentally satisfiable.
    """
    dt = Datatype("Unit", ctx=ctx)
    dt.declare("unit")
    sort = dt.create()
    return sort, sort.unit


_unit_sort_ref, _unit_value = _build_unit_sort(main_ctx())
sort_cache["Unit"] = _unit_sort_ref

# Caches for the SMT-context helpers. Within a single solve, `translate` is
# called repeatedly with constraints that share the same underlying SMTContext,
# so the `variables`, `functions`, and `sorts` collections are the same Python
# objects across many calls. We key by `id` because dict/list are not hashable;
# the cached dict is held strongly so the id cannot be reused while cached.
_mk_vars_cache: dict[int, tuple[dict[str, TypeConstructor], dict[str, Any]]] = {}
_mk_funs_cache: dict[int, tuple[dict[str, AbstractionType], dict[str, Any]]] = {}
_mk_sorts_cache: dict[tuple[str, ...], dict[str, SortRef]] = {}
_SMT_HELPER_CACHE_MAX = 1024


# The main thread's per-thread state: a view over the default-context module
# globals built above, so main-thread behaviour is byte-identical to before.
_MAIN = _WS()
_MAIN.ctx = main_ctx()
_MAIN.solver = s
_MAIN.sort_cache = sort_cache
_MAIN.base_functions = base_functions
_MAIN.unit_sort = _unit_sort_ref
_MAIN.unit_value = _unit_value
_MAIN.mk_vars = _mk_vars_cache
_MAIN.mk_funs = _mk_funs_cache
_MAIN.mk_sorts = _mk_sorts_cache
_MAIN.ple = _ple_cache


def _bound(cache: dict, limit: int = _SMT_HELPER_CACHE_MAX) -> None:
    if len(cache) > limit:
        # Drop ~10% oldest entries (insertion order in CPython dicts).
        drop = max(1, limit // 10)
        for k in list(cache.keys())[:drop]:
            del cache[k]


def mk_vars(
    variables: dict[str, TypeConstructor], sorts: dict[str, SortRef], ws: "_WS | None" = None
) -> dict[str, Any]:
    ws = ws or _ws()
    cache = ws.mk_vars
    key = id(variables)
    hit = cache.get(key)
    if hit is not None and hit[0] is variables:
        return hit[1]
    result = {name: make_variable(name, base, ws) for name, base in variables.items()}
    cache[key] = (variables, result)
    _bound(cache)
    return result


def get_sort(base: Type, ws: "_WS | None" = None) -> SortRef:
    ws = ws or _ws()
    ctx = ws.ctx
    match base:
        case Top() | TypeConstructor(Name("Top", _)):
            return IntSort(ctx)
        case TypeConstructor(Name("Unit", _)):
            return ws.unit_sort
        case TypeConstructor(Name("Int", _)):
            return IntSort(ctx)
        case TypeConstructor(Name("Bool", _)):
            return BoolSort(ctx)
        case TypeConstructor(Name("Float", _)):
            return RealSort(ctx)
        case TypeConstructor(Name("String", _)):
            return StringSort(ctx)
        case TypeConstructor(Name("Set", _)):
            return _set_sort(ctx)
        case TypeConstructor(name, args):
            sname = _mangle_sort_name(base) if args else str(name)
            if sname[:1].isupper():
                if sname not in ws.sort_cache:
                    ws.sort_cache[sname] = DeclareSort(sname, ctx)
                return ws.sort_cache[sname]
            return IntSort(ctx)
        case TypeVar(name):
            assert False, f"TypeVar {name} should not be used in SMT solver."
        case _:
            raise Exception(f"SMT sort of {base} not implemented.")


def unrefine_type(base: Type):
    """Removes refinements from type."""
    match base:
        case RefinedType(_, ty, _):
            return ty
        case AbstractionType(name, aty, rty):
            return AbstractionType(name, unrefine_type(aty), unrefine_type(rty))
        case TypePolymorphism(name, kind, body):
            return TypePolymorphism(name, kind, unrefine_type(body))
        case TypeConstructor(name, args):
            return TypeConstructor(name, [unrefine_type(a) for a in args])

        case _:
            return base


class UncurryError(Exception):
    """A function type's shape couldn't be flattened into ``([sort], sort)``.

    Raised by :func:`uncurry` when an argument or return position holds a
    type the SMT layer doesn't know how to project onto a Z3 sort.
    ``mk_funs`` catches this specifically so it can skip the polymorphic
    template (the per-call-site monomorphised twin always succeeds).
    """


def uncurry(base: AbstractionType) -> tuple[list[TypeConstructor], TypeConstructor]:
    current: Type = unrefine_type(base)
    inputs = []
    vars_to_remove = []

    while isinstance(current, TypePolymorphism):
        vars_to_remove.append(current.name)
        current = current.body

    while isinstance(current, AbstractionType):
        match current.var_type:
            case TypeConstructor(_, _):
                # Preserve parametric type-constructor args; ``get_sort``
                # mangles them into a per-instantiation Z3 sort.
                inputs.append(current.var_type)
            case Top():
                inputs.append(t_unit)
            case TypeVar(name):
                if name in vars_to_remove:
                    inputs.append(t_int)
                else:
                    inputs.append(TypeConstructor(name))
            case AbstractionType(_, _, _) | TypePolymorphism(_, _, _) | RefinementPolymorphism(_, _, _):
                inputs.append(t_int)
            case _:
                raise UncurryError(f"Unknown SMT type {current.var_type} in {base}.")
        current = current.type

    if isinstance(current, Top):
        current = t_unit
    if isinstance(current, TypeVar):
        # A polymorphic return that wasn't specialised — represent it as
        # an opaque sort named after the type variable.
        current = TypeConstructor(current.name)
    if not isinstance(current, TypeConstructor):
        raise UncurryError(f"Unknown SMT return type {current} in {base}.")
    return (inputs, current)


def make_variable(name: str, base: TypeConstructor | AbstractionType | Top, ws: "_WS | None" = None) -> Any:
    ws = ws or _ws()
    ctx = ws.ctx
    match base:
        case Top():
            return Int(name, ctx)
        case TypeConstructor(Name("Unit", _)):
            return Const(name, ws.unit_sort)
        case TypeConstructor(Name("Int", _)):
            return Int(name, ctx)
        case TypeConstructor(Name("Bool", _)):
            return Bool(name, ctx)
        case TypeConstructor(Name("Float", _), _):
            return Real(name, ctx)
        case TypeConstructor(Name("String", _)):
            return String(name, ctx)
        case TypeConstructor(Name("Set", _)):
            return Const(name, _set_sort(ctx))
        case TypeConstructor(Name("Top", _)):
            return Int(name, ctx)
        case TypeConstructor(_, _):
            return Const(name, get_sort(base, ws))
        case TypeVar(_):
            return Int(name, ctx)
        case AbstractionType(_, _, _):
            if name in ws.base_functions:
                return ws.base_functions[name]
            else:
                input_types, output_type = uncurry(base)
                args = [get_sort(x, ws) for x in input_types] + [get_sort(output_type, ws)]
                return Function(name, *args)
        case _:
            assert False, f"No var: {name}, with base {base}."


def _coerce_numeric(a: Any, ctx) -> Any:
    """Lift a Python numeric literal into the matching Z3 value so that an
    operation on it uses Z3 semantics rather than Python's. Z3 expressions (and
    anything non-numeric) pass through unchanged. ``bool`` is checked first
    since it is a subclass of ``int``."""
    if isinstance(a, bool):
        return a
    if isinstance(a, int):
        return IntVal(a, ctx)
    if isinstance(a, float):
        return RealVal(a, ctx)
    return a


def translate_liq(
    t: LiquidTerm,
    variables: dict[str, Any],
    memo: dict[int, tuple[LiquidTerm, Any]] | None = None,
    ws: "_WS | None" = None,
):
    """Translate a ``LiquidTerm`` into a Z3 expression.

    ``memo`` (optional) caches already-translated subterms by object identity
    so a shared subtree is translated once. A single ``smt_valid`` run flattens
    one constraint into many ``CanonicConstraint``s that share an *accumulated
    premise* (the same ``h_i == e_i`` term objects recur in every conjunct), so
    without memoization those affine premises are re-walked once per conjunct —
    the dominant cost on large obligations (e.g. the NN robustness queries in
    ``examples/nn/mnist``).

    Soundness of reusing a cached AST across the conjuncts of one solve: every
    binder is alpha-renamed to a globally fresh name (so a name has a single
    sort throughout the run) and Z3 hash-conses constants/functions by
    name+sort, so a given term object always denotes the same Z3 AST regardless
    of which constraint's ``variables`` dict is in hand. The cache also keeps a
    strong reference to each key term (``hit[0] is t`` guards against ``id``
    recycling), and it is scoped to one ``smt_valid`` call. Without ``memo``
    (external callers) behaviour is identical to before.
    """
    if ws is None:
        ws = _ws()
    if memo is None:
        return _translate_liq(t, variables, None, ws)
    tid = id(t)
    hit = memo.get(tid)
    if hit is not None and hit[0] is t:
        return hit[1]
    result = _translate_liq(t, variables, memo, ws)
    memo[tid] = (t, result)
    return result


def _translate_liq(t: LiquidTerm, variables: dict[str, Any], memo: dict[int, tuple[LiquidTerm, Any]] | None, ws: "_WS"):
    base_functions = ws.base_functions
    match t:
        case LiquidLiteralBool(b):
            return b
        case LiquidLiteralInt(i):
            return i
        case LiquidLiteralFloat(f):
            return f
        case LiquidLiteralString(s):
            # Z3 auto-casts Python int/bool/float into its sorts when a literal
            # appears as an argument, but Python `str` does not auto-cast to
            # Z3's String sort, so convert explicitly.
            return StringVal(s, ws.ctx)
        case LiquidLiteralUnit():
            # The single inhabitant of the dedicated Unit datatype.
            return ws.unit_value
        case LiquidVar(name):
            sname = str(name)
            if sname in variables:
                return variables[sname]
            if sname in base_functions:
                return base_functions[sname]
            raise KeyError(f"Variable {sname} not found in SMT context")
        case LiquidHornApplication(name, args):
            assert False, "LiquidHornApplication should not get to SMT solver!"
        case LiquidApp(fun_name, args):
            fun = base_functions.get(fun_name.name, variables.get(str(fun_name), None))
            assert fun is not None, f"Function {fun_name} not found." + str(variables)
            args = [translate_liq(a, variables, memo, ws) for a in args]
            if fun_name.name in ("/", "%"):
                # Evaluate division and modulo with Z3 numeric semantics, not
                # Python's. On two Python int literals, Python's ``/`` is *float*
                # division (so ``6 / 2`` is ``3.0`` -- an unsound mismatch with
                # the Int type) and raises ``ZeroDivisionError`` on a zero
                # divisor (which used to silently drop the obligation, letting
                # absurd refinements through). Coercing the operands into Z3
                # makes ``/`` and ``%`` total integer operations, and division
                # by zero a fixed-but-unconstrained Z3 term that no refinement
                # can exploit.
                args = [_coerce_numeric(a, ws.ctx) for a in args]
            try:
                return fun(*args)
            except Z3Exception as e:
                raise e

        case _:
            assert False, f"Cannot translate {t}."


def mk_sorts(sorts: list[str], ws: "_WS | None" = None) -> dict[str, SortRef]:
    ws = ws or _ws()
    cache = ws.mk_sorts
    key = tuple(sorts)
    hit = cache.get(key)
    if hit is not None:
        return hit
    result = {name: get_sort(TypeConstructor(Name(name, 0)), ws) for name in sorts}
    cache[key] = result
    _bound(cache)
    return result


def mk_funs(
    functions: dict[str, AbstractionType], sorts: dict[str, SortRef], ws: "_WS | None" = None
) -> dict[str, Any]:
    ws = ws or _ws()
    cache = ws.mk_funs
    key = id(functions)
    hit = cache.get(key)
    if hit is not None and hit[0] is functions:
        return hit[1]
    funs = {}
    for name, ty in functions.items():
        try:
            input_types, output_type = uncurry(ty)
        except UncurryError:
            # The polymorphic template can't be projected onto Z3 sorts.
            # ``_specialize_liquid_term`` emits a monomorphised twin per
            # call site that ``uncurry`` *can* process; that twin gets
            # picked up the next time this loop runs.
            continue
        args = [sorts.get(str(x), get_sort(x, ws)) for x in input_types] + [
            sorts.get(str(output_type), get_sort(output_type, ws))
        ]
        funs[name] = Function(name, *args)
    cache[key] = (functions, funs)
    _bound(cache)
    return funs


def _constructor_distinctness(variables: dict[str, Any]) -> list[BoolRef]:
    """Generate Distinct(...) assertions for constructor constants of the same inductive type."""
    from aeon.verification.constructor_registry import get_constructor_groups

    # Build reverse lookup: base name (no ID suffix) -> SMT variable
    # Variable keys include superscript IDs (e.g. "Pizza_margherita⁷"),
    # but the registry stores plain names (e.g. "Pizza_margherita").
    base_to_var: dict[str, Any] = {}
    for key, val in variables.items():
        # Strip any trailing superscript digits (Unicode superscripts ⁰-⁹)
        base = key.rstrip("⁰¹²³⁴⁵⁶⁷⁸⁹")
        base_to_var[base] = val

    assertions: list[BoolRef] = []
    for _type_name, ctor_names in get_constructor_groups().items():
        present = [base_to_var[n] for n in ctor_names if n in base_to_var]
        if len(present) >= 2:
            assertions.append(Distinct(*present))
    return assertions


def translate(
    c: CanonicConstraint,
    memo: dict[int, tuple[LiquidTerm, Any]] | None = None,
) -> BoolRef | bool:
    ws = _ws()
    sorts = mk_sorts(c.sorts, ws)
    functions = mk_funs(c.functions, sorts, ws)
    variables = mk_vars(c.variables, sorts, ws)
    env = variables | functions
    e1 = translate_liq(c.premise, env, memo, ws)
    e2 = translate_liq(c.conclusion, env, memo, ws)
    if isinstance(e2, bool) and e2 is True:
        return False
    if isinstance(e1, bool) and isinstance(e2, bool):
        return e1 and not e2
    # A premise/conclusion that reduces to a Python ``bool`` must be lifted into
    # *this thread's* Z3 context: ``Not(False)`` (etc.) with no context falls back
    # to the default ``main_ctx``, which then clashes with the worker-context
    # ``premise`` in the ``And`` below ("Context mismatch"). On the main thread
    # ``ws.ctx`` *is* the default context, so this is a no-op there.
    if isinstance(e1, bool):
        e1 = BoolVal(e1, ws.ctx)
    if isinstance(e2, bool):
        e2 = BoolVal(e2, ws.ctx)
    distinct = _constructor_distinctness(variables)
    premise = And(e1, *distinct) if distinct else e1
    return And(premise, Not(e2))
