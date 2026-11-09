from __future__ import annotations

import weakref
from typing import Callable

from aeon.core.equality import core_type_equality
from aeon.core.instantiation import type_substitution
from aeon.core.liquid import LiquidApp, LiquidPredicate, LiquidVar
from aeon.core.substitutions import instantiate_refinement_in_type
from aeon.core.terms import (
    Abstraction,
    Application,
    ImplicitRefinementHole,
    Let,
    Literal,
    RefinementApplication,
    Term,
    TypeApplication,
    Var,
)
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    RefinementPolymorphism,
    Type,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
    refined_to_unrefined_type,
    t_bool,
    t_float,
    t_int,
    t_string,
)
from aeon.decorators.api import Metadata
from aeon.synthesis.grammar.utils import SYNTHESIS_EXCLUDED_NAMES
from aeon.synthesis.grammar.poly import predicate_argument
from aeon.typechecking.branch_evidence import stored_match_predicate, unconstrained_predicate
from aeon.typechecking.context import TypingContext
from aeon.typechecking.entailment import entailment
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name, fresh_counter
from aeon.verification.sub import sub

_loc = SynthesizedLocation("tdsyn")


# Subtype results are stable for a given TypingContext object identity. Keyed
# by ``id(ctx)`` with a ``weakref.finalize`` hook that evicts the per-context
# bucket when the context is garbage collected, so a later context reusing the
# same address can never observe stale results. Also cleared at the start of
# each native synthesis run via :func:`clear_tdsyn_caches`.
_subtype_cache: dict[int, dict[tuple[str, str], bool]] = {}


def clear_tdsyn_caches() -> None:
    """Drop memoized subtype / component-library results for a fresh search."""
    from aeon.synthesis.modules.tdsyn.incremental import clear_incremental_queries

    clear_incremental_queries()
    _subtype_cache.clear()
    from aeon.synthesis.modules.tdsyn.library import clear_component_library_cache

    clear_component_library_cache()


def is_subtype(ctx: TypingContext, t1: Type, t2: Type) -> bool:
    """Check if t1 is a subtype of t2, with cheap short-circuits and a cache.

    Equal types, forgetting a refinement, and mismatched base constructors avoid
    SMT; all other pairs go through ``sub`` / ``entailment`` once per
    ``(ctx, t1, t2)`` triple.
    """
    if t1 == t2 or (isinstance(t1, RefinedType) and t1.type == t2):
        return True
    b1 = base_type_of(t1)
    b2 = base_type_of(t2)
    if b1 is not None and b2 is not None and b1.name.name != b2.name.name:
        return False

    ctx_key = id(ctx)
    bucket = _subtype_cache.get(ctx_key)
    if bucket is None:
        bucket = {}
        _subtype_cache[ctx_key] = bucket
        weakref.finalize(ctx, _subtype_cache.pop, ctx_key, None)
    key = (repr(t1), repr(t2))
    cached = bucket.get(key)
    if cached is not None:
        return cached
    constraint = sub(ctx, t1, t2)
    result = entailment(ctx, constraint)
    bucket[key] = result
    return result


def base_type_of(ty: Type) -> TypeConstructor | None:
    """Strip refinements to get the base TypeConstructor, or None if not a base type."""
    unrefined = refined_to_unrefined_type(ty)
    match unrefined:
        case TypeConstructor():
            return unrefined
        case _:
            return None


def get_return_type(ty: Type) -> Type:
    """Get the final return type of a (possibly multi-argument) function type."""
    t = ty
    while isinstance(t, AbstractionType):
        t = t.type
    return t


def get_param_types(ty: Type) -> list[tuple[Name, Type]]:
    """Extract (name, type) for each parameter of a function type."""
    params: list[tuple[Name, Type]] = []
    t = ty
    while isinstance(t, AbstractionType):
        params.append((t.var_name, t.var_type))
        t = t.type
    return params


def bases_match(t1: Type, t2: Type) -> bool:
    """Fast structural pre-check: do the base type constructors match?"""
    left, right = refined_to_unrefined_type(t1), refined_to_unrefined_type(t2)
    if isinstance(left, TypeVar) or isinstance(right, TypeVar):
        return left == right
    b1 = base_type_of(t1)
    b2 = base_type_of(t2)
    if b1 is None or b2 is None:
        return False
    return b1.name.name == b2.name.name


def should_skip(name: Name, fun_name: Name, metadata: Metadata, is_recursion_allowed: bool) -> bool:
    """Check if a variable should be skipped during synthesis."""
    if name == fun_name:
        return not is_recursion_allowed
    if name.name in SYNTHESIS_EXCLUDED_NAMES:
        return True
    return False


BUILTIN_BASE_TYPES: list[TypeConstructor] = [t_int, t_bool, t_float, t_string]

# Prelude arithmetic / comparison ops are ``forall a:B``, but only Int/Float
# (and Bool/String for equality) have runtime/liquid meaning. Instantiating
# them at every in-scope ADT (``(+)[Arch]``, ``(==)[Circuit]``, …) floods
# constructor-only holes with type-ok junk.
_NUMERIC_OPS = frozenset({"+", "-", "*", "/", "%", "<", ">", "<=", ">="})
_EQUALITY_OPS = frozenset({"==", "!="})
_NUMERIC_MONO_TYPES: list[TypeConstructor] = [t_int, t_float]
_EQUALITY_MONO_TYPES: list[TypeConstructor] = [t_int, t_float, t_bool, t_string]


def _collect_concrete_types(ctx: TypingContext) -> list[TypeConstructor]:
    """Collect all concrete base types from context plus built-ins."""
    types: set[str] = set()
    result: list[TypeConstructor] = []
    for tc in BUILTIN_BASE_TYPES:
        if tc.name.name not in types:
            types.add(tc.name.name)
            result.append(tc)
    for _, t in ctx.concrete_vars():
        bt = base_type_of(t)
        if bt is not None and bt.name.name not in types and bt != TypeConstructor(Name("Unit", 0)):
            types.add(bt.name.name)
            result.append(bt)
    return result


def _mono_types_for(name: Name, ctx: TypingContext) -> list[TypeConstructor]:
    """Concrete types to instantiate ``name``'s type variables with."""
    if name.name in _NUMERIC_OPS:
        return list(_NUMERIC_MONO_TYPES)
    if name.name in _EQUALITY_OPS:
        return list(_EQUALITY_MONO_TYPES)
    return _collect_concrete_types(ctx)


def monomorphize(name: Name, ty: Type, ctx: TypingContext, goal: Type | None = None) -> list[tuple[Term, Type]]:
    """Generate all monomorphic instantiations of a (possibly polymorphic) type.

    Returns list of (term, monomorphic_type) pairs.
    For non-polymorphic types, returns [(Var(name), ty)].
    For polymorphic types, instantiates type variables with concrete types from context.
    Retained result relations are instantiated from ``goal`` when available.
    Other abstract predicates remain implicit for final Horn inference, with
    an arity-correct unconstrained approximation used during search.
    """
    return _monomorphize_term(Var(name, _loc), ty, ctx, _mono_types_for(name, ctx), goal)


def _result_predicate(body: Type, name: Name, sort: Type, goal: Type | None) -> LiquidPredicate | None:
    """Match a retained predicate variable to the corresponding goal argument.

    Match by the predicate's identity in the result, not quantifier position:
    helpers can reorder relation parameters. Compound relation expressions
    are left to inference rather than treating them as bare parameters.
    """
    if goal is None:
        return None
    while isinstance(body, (TypePolymorphism, RefinementPolymorphism, AbstractionType)):
        body = body.type if isinstance(body, AbstractionType) else body.body
    result, target = base_type_of(body), base_type_of(goal)
    if (
        result is None
        or target is None
        or not core_type_equality(TypeConstructor(result.name, result.args), TypeConstructor(target.name, target.args))
    ):
        return None
    for index, predicate in enumerate(result.refinements):
        direct = not predicate.parameters and predicate.body == LiquidVar(name)
        eta = predicate.body == LiquidApp(name, [LiquidVar(p) for p in predicate.parameters])
        if (direct or eta) and index < len(target.refinements):
            return stored_match_predicate(target, index, sort)
    return None


def _monomorphize_term(
    base_term: Term,
    ty: Type,
    ctx: TypingContext,
    concrete_types: list[TypeConstructor],
    goal: Type | None = None,
) -> list[tuple[Term, Type]]:
    """Continue monomorphizing an already partially applied term."""
    match ty:
        case TypePolymorphism(var_name, _, body):
            results: list[tuple[Term, Type]] = []
            for concrete_type in concrete_types:
                substituted = type_substitution(body, var_name, concrete_type)
                applied: Term = TypeApplication(base_term, concrete_type, _loc)
                results.extend(_monomorphize_term(applied, substituted, ctx, concrete_types, goal))
            return results
        case RefinementPolymorphism(pred_name, sort, body):
            predicate = _result_predicate(body, pred_name, sort, goal)
            if predicate is None:
                argument: Term = ImplicitRefinementHole(Name("_pred", fresh_counter.fresh()), _loc)
                replacement: Abstraction | LiquidPredicate = unconstrained_predicate(sort)
            else:
                argument = predicate_argument(ctx, predicate, sort)
                replacement = predicate
            applied = RefinementApplication(base_term, argument, _loc)
            substituted = instantiate_refinement_in_type(body, pred_name, replacement)
            return _monomorphize_term(applied, substituted, ctx, concrete_types, goal)
        case _:
            return [(base_term, ty)]


def make_skip_fn(fun_name: Name, metadata: Metadata) -> Callable[[Name], bool]:
    """Create a skip function for use in actions."""
    current_metadata = metadata.get(fun_name, {})
    is_recursion_allowed = current_metadata.get("recursion", False)

    def skip(name: Name) -> bool:
        return should_skip(name, fun_name, metadata, is_recursion_allowed)

    return skip


def is_constructor_term(term: Term) -> bool:
    """Recognize a registered constructor through applications and instantiation."""
    from aeon.verification.constructor_registry import get_constructor_groups

    while isinstance(term, (Application, TypeApplication, RefinementApplication)):
        term = term.fun if isinstance(term, Application) else term.body
    return isinstance(term, Var) and any(term.name.name in names for names in get_constructor_groups().values())


def bind_constructor_arguments(term: Term) -> Term:
    """Name intermediate data values before checking dependent measure types.

    A nested constructor argument is otherwise substituted into every use of
    its measures, making deep list proofs expand dramatically. Only pure data
    trees are rewritten; calls and control flow keep their evaluation order.
    """

    def spine(value: Term) -> tuple[Term, list[Term]]:
        args = []
        while isinstance(value, Application):
            args.append(value.arg)
            value = value.fun
        return value, list(reversed(args))

    def data_tree(value: Term) -> bool:
        if isinstance(value, (Literal, Var)):
            return True
        return is_constructor_term(value) and all(data_tree(arg) for arg in spine(value)[1])

    if not is_constructor_term(term) or not data_tree(term):
        return term
    bindings: list[tuple[Name, Term]] = []

    def bind(value: Term) -> Var:
        name = Name("_data", fresh_counter.fresh())
        bindings.append((name, value))
        return Var(name, _loc)

    def visit(value: Term) -> Term:
        head, args = spine(value)
        for arg in args:
            if is_constructor_term(arg):
                # Evaluate earlier curried applications before this argument,
                # even if a local function shadows a registered constructor.
                atomic_head = head
                while isinstance(atomic_head, (TypeApplication, RefinementApplication)):
                    atomic_head = atomic_head.body
                if not isinstance(atomic_head, Var):
                    head = bind(head)
                arg = bind(visit(arg))
            head = Application(head, arg, value.loc)
        return head

    result = visit(term)
    for name, value in reversed(bindings):
        result = Let(name, value, result, _loc)
    return result
