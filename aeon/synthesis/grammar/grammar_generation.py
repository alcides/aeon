from __future__ import annotations

from abc import ABC
from dataclasses import make_dataclass
from typing import Generator, Optional, Tuple, Protocol
from typing import Type as TypingType

from geneticengine.grammar import extract_grammar, Grammar
from geneticengine.grammar.decorators import weight
from geneticengine.grammar.metahandlers.base import MetaHandlerGenerator
from geneticengine.prelude import abstract

from aeon.core.liquid import (
    LiquidApp,
    LiquidHole,
    LiquidLiteralBool,
    LiquidLiteralFloat,
    LiquidLiteralInt,
    LiquidLiteralString,
    LiquidLiteralUnit,
    LiquidTerm,
    LiquidVar,
)
from itertools import product

from aeon.core.equality import canonicalize_type
from aeon.core.substitutions import substitute_vartype, substitution_in_type, substitution_liquid_in_type
from aeon.core.terms import Abstraction, Annotation, Application, If, Literal, TypeApplication
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, RefinementPolymorphism, Type, TypePolymorphism, TypeVar
from aeon.core.types import TypeConstructor
from aeon.core.types import RefinedType
from aeon.core.types import Top
from aeon.core.types import refined_to_unrefined_type
from aeon.core.types import t_bool
from aeon.core.types import t_float
from aeon.core.types import t_int
from aeon.core.types import t_string
from aeon.decorators import Metadata
from aeon.synthesis.grammar.mangling import mangle_name, mangle_var, mangle_type
from aeon.synthesis.grammar.refinements import refined_type_to_metahandler
from aeon.synthesis.grammar.utils import prelude_ops, aeon_to_python
from aeon.typechecking.context import (
    TypeBinder,
    TypeConstructorBinder,
    TypingContext,
    TypingContextEntry,
    UninterpretedBinder,
    VariableBinder,
)
from aeon.core.liquid_ops import ops
from aeon.utils.name import Name, fresh_counter


VAR_WEIGHT = 10000
LITERAL_WEIGHT = 3000
IF_WEIGHT = 1
APP_WEIGHT = 1000
ABS_WEIGHT = 100


def strip_refinements_keep_arg_refinements(ty: Type) -> Type:
    """Like ``refined_to_unrefined_type`` but preserves refinements on the
    argument positions of an abstraction chain.

    Refinements on inductive-constructor argument positions (e.g.
    ``Chunk_hill_chunk : {x:Int | x >= 5 && x <= 95} -> ... -> Chunk``)
    are the only signal the grammar generator has for sampling ints within
    the constructor's required range. Stripping them away makes the search
    plug random ints from the global ``[-1, 256]`` default into refined
    slots, which almost never type-checks.
    """
    if isinstance(ty, RefinedType):
        return ty.type
    if isinstance(ty, AbstractionType):
        return AbstractionType(
            ty.var_name,
            ty.var_type,
            strip_refinements_keep_arg_refinements(ty.type),
        )
    return ty


def extract_class_name(class_name: str) -> str:
    prefixes = [
        "var_",
        "app_",
        "refined_app_",
        "refined_var_",
        "literal_Refined_",
        "literal_",
    ]
    for prefix in prefixes:
        if class_name.startswith(prefix):
            return class_name[len(prefix) :]
    return class_name


class GrammarError(Exception):
    pass


# Protocol for classes that can have a get_core method
class HasGetCore(Protocol):
    def get_core(self): ...


classType = TypingType[HasGetCore]


def is_valid_class_name(class_name: str) -> bool:
    return class_name not in prelude_ops and not class_name.startswith("target")


ae_top = type("ae_top", (ABC,), {})


def _key(ty: Type) -> Type:
    """Canonical (alpha-equivalence) key used for all ``type_info`` lookups."""
    return canonicalize_type(ty)


def _get(type_info: dict[Type, TypingType], ty: Type) -> TypingType:
    return type_info[_key(ty)]


def _has(type_info: dict[Type, TypingType], ty: Type) -> bool:
    return _key(ty) in type_info


def extract_all_types(
    types: list[Type],
    ctx: Optional[TypingContext] = None,
    instantiation_types: Optional[set[TypeConstructor]] = None,
) -> dict[Type, TypingType]:
    if instantiation_types is None:
        instantiation_types = set()
    data: dict[Type, TypingType] = {_key(Top()): ae_top}
    # Iterate ``types`` in the given order (deduplicating via ``data``) rather
    # than through a set comprehension: the class-creation order here determines
    # ``__subclasses__()`` order, and hence the grammar's production order, so a
    # set would make seeded generation non-deterministic across processes.
    for t in types:
        ty = _key(t)
        if ty not in data:
            match ty:
                case TypeConstructor(_, args):
                    if args:
                        data.update(extract_all_types(list(args), ctx, instantiation_types))
                    class_name = mangle_type(ty)
                    ty_abstract_class = type(
                        class_name,
                        (ae_top, ABC),
                        {},
                    )
                    ty_abstract_class = abstract(ty_abstract_class)
                    data[ty] = ty_abstract_class
                case RefinedType(_, itype, _):
                    class_name = mangle_type(ty)
                    data.update(extract_all_types([itype], ctx, instantiation_types))
                    parent = _get(data, itype)
                    ty_abstract_class = type(class_name, (parent, ABC), {})
                    ty_abstract_class = abstract(ty_abstract_class)
                    data[ty] = ty_abstract_class
                    # Refined-type subtyping is wired by wire_refined_subtyping
                    # in a post-pass once all refined classes exist (#312).
                case AbstractionType(var_name, var_type, return_type):
                    class_name = mangle_type(ty)
                    data.update(
                        extract_all_types(
                            [var_type, substitution_in_type(return_type, Var(Name("__self__", 0)), var_name)],
                            ctx,
                            instantiation_types,
                        )
                    )
                    ty_abstract_class = type(class_name, (ae_top, ABC), {})
                    ty_abstract_class = abstract(ty_abstract_class)
                    data[ty] = ty_abstract_class
                case Top():
                    data[ty] = ae_top
                case TypePolymorphism(_, _, _):
                    # Monomorphize the forall over the program-derived instantiation
                    # types and register a grammar class for each concrete body.
                    # We deliberately do NOT register a class for the forall node
                    # itself (`mangle_type` asserts on TypePolymorphism).
                    # RefinementPolymorphism bodies are intentionally skipped:
                    # `monomorphize_poly_type` returns [] for them (and for an
                    # empty instantiation set), making this a graceful no-op.
                    for mono_body, _ in monomorphize_poly_type(ty, instantiation_types):
                        data.update(extract_all_types([mono_body], ctx, instantiation_types))
                case TypeVar():
                    # Free/unbound type variable: nothing concrete to register.
                    continue
                case _:
                    assert False, f"Unsupported {ty}"
    # When a TypingContext is available, model subtyping among refined types by
    # rewiring the refined classes that share a base into a single linear
    # inheritance chain (a linear extension of the subtype partial order).
    # When ctx is None this pass is skipped entirely (preserves legacy behaviour
    # and keeps tests that call extract_all_types without a context green).
    if ctx is not None:
        wire_refined_subtyping(data, ctx)
    return data


# --- Refined-type subtyping (issue #312, Stage 1: syntactic intervals) -------
#
# geneticengine registers a node as an alternative of its ``mro()[1]`` only (its
# single first base). Refined classes sharing a base must therefore form a
# single linear inheritance chain: each refined class's first base is the
# next-wider class, bottoming out at the base type's class. Listing a base
# before its descendant raises "Cannot create a consistent method resolution
# order"; bases must be most-derived-first, then ABC. We never add the base type
# explicitly alongside a refined parent.

# An interval over a single refinement variable, represented as
# (low, low_inclusive, high, high_inclusive) with None meaning unbounded.
RefInterval = Tuple[Optional[float], bool, Optional[float], bool]

_FULL_INTERVAL: RefInterval = (None, False, None, False)


def _literal_value(lt: LiquidTerm) -> Optional[float]:
    match lt:
        case LiquidLiteralInt(v) | LiquidLiteralFloat(v):
            return v
        case _:
            return None


def _atom_to_interval(lt: LiquidTerm, var: Name) -> Optional[RefInterval]:
    """Parse a single comparison atom over ``var`` against a numeric literal
    into an interval. Returns None if the atom is not a recognised one-sided
    comparison of the form ``var OP const`` or ``const OP var`` (Int/Float)."""
    match lt:
        case LiquidApp(Name(op, _), [left, right]) if op in ("<", "<=", ">", ">="):
            lv = _literal_value(left)
            rv = _literal_value(right)
            # var OP const
            if isinstance(left, LiquidVar) and left.name == var and rv is not None:
                if op == "<":
                    return (None, False, rv, False)
                if op == "<=":
                    return (None, False, rv, True)
                if op == ">":
                    return (rv, False, None, False)
                if op == ">=":
                    return (rv, True, None, False)
            # const OP var  (flip the operator)
            if isinstance(right, LiquidVar) and right.name == var and lv is not None:
                if op == "<":
                    return (lv, False, None, False)
                if op == "<=":
                    return (lv, True, None, False)
                if op == ">":
                    return (None, False, lv, False)
                if op == ">=":
                    return (None, False, lv, True)
            return None
        case _:
            return None


def _intersect_low(a: Tuple[Optional[float], bool], b: Tuple[Optional[float], bool]) -> Tuple[Optional[float], bool]:
    (la, ia), (lb, ib) = a, b
    if la is None:
        return (lb, ib)
    if lb is None:
        return (la, ia)
    if la > lb:
        return (la, ia)
    if lb > la:
        return (lb, ib)
    return (la, ia and ib)  # equal bound: tighter is the exclusive one


def _intersect_high(a: Tuple[Optional[float], bool], b: Tuple[Optional[float], bool]) -> Tuple[Optional[float], bool]:
    (ha, ia), (hb, ib) = a, b
    if ha is None:
        return (hb, ib)
    if hb is None:
        return (ha, ia)
    if ha < hb:
        return (ha, ia)
    if hb < ha:
        return (hb, ib)
    return (ha, ia and ib)


def refinement_to_interval(ty: RefinedType) -> Optional[RefInterval]:
    """Best-effort parse of a refinement into a single interval over the bound
    variable, handling conjunctions of one-sided literal comparisons (e.g.
    ``c1 <= x && x <= c2`` and one-sided ``<,<=,>,>=``).

    Returns None when the refinement contains anything not recognised (e.g.
    disjunctions, non-literal bounds, user functions), so the caller can fall
    back to the conservative behaviour of adding no extra subtyping edge.
    """
    var = ty.name

    def go(lt: LiquidTerm) -> Optional[RefInterval]:
        match lt:
            case LiquidApp(Name("&&", _), [a, b]):
                ia = go(a)
                ib = go(b)
                if ia is None or ib is None:
                    return None
                low = _intersect_low((ia[0], ia[1]), (ib[0], ib[1]))
                high = _intersect_high((ia[2], ia[3]), (ib[2], ib[3]))
                return (low[0], low[1], high[0], high[1])
            case _:
                return _atom_to_interval(lt, var)

    return go(ty.refinement)


def _ge_low(a: Tuple[Optional[float], bool], b: Tuple[Optional[float], bool]) -> bool:
    """Is low-bound ``a`` at least as tight (>=) as low-bound ``b``?"""
    (la, ia), (lb, ib) = a, b
    if lb is None:
        return True  # b imposes no lower bound
    if la is None:
        return False  # a imposes none but b does
    if la > lb:
        return True
    if la < lb:
        return False
    # equal numeric bound: a is tighter iff it is exclusive while b is inclusive,
    # or they share inclusivity.
    return (not ia) or ib


def _le_high(a: Tuple[Optional[float], bool], b: Tuple[Optional[float], bool]) -> bool:
    """Is high-bound ``a`` at least as tight (<=) as high-bound ``b``?"""
    (ha, ia), (hb, ib) = a, b
    if hb is None:
        return True
    if ha is None:
        return False
    if ha < hb:
        return True
    if ha > hb:
        return False
    return (not ia) or ib


def interval_subset(a: RefInterval, b: RefInterval) -> bool:
    """Is interval ``a`` contained in interval ``b`` (a's values all satisfy b)?"""
    return _ge_low((a[0], a[1]), (b[0], b[1])) and _le_high((a[2], a[3]), (b[2], b[3]))


def wire_refined_subtyping(data: dict[Type, TypingType], ctx: TypingContext) -> None:
    """Rewire refined classes sharing a base into linear inheritance chains so
    that geneticengine can reach narrower refinements from wider ones.

    Stage 1 (issue #312) decides subtyping with a purely syntactic
    literal-interval-containment rule over Int/Float refinements. Refinements it
    cannot analyse simply get no extra edge (they keep inheriting directly from
    the base class, as built in ``extract_all_types``).
    """
    # Group refined keys by their (unrefined) base type.
    groups: dict[Type, list[RefinedType]] = {}
    for ty in data:
        if isinstance(ty, RefinedType):
            groups.setdefault(ty.type, []).append(ty)

    for base_type, refined in groups.items():
        if base_type not in data:
            continue
        # Only handle refinements we can turn into intervals; others are left
        # attached directly to the base class.
        analysable: dict[RefinedType, RefInterval] = {}
        for rt in refined:
            iv = refinement_to_interval(rt)
            # TODO(#312 stage 2): SMT entailment fallback for refinements the
            # interval analyzer cannot decide (iv is None). For now, leave them
            # attached to the base class (current behaviour, no extra edge).
            if iv is not None:
                analysable[rt] = iv
        if len(analysable) < 2:
            continue

        # Collapse mutual-containment equivalence classes (e.g. x>0 vs x>=1 over
        # Int are structurally different but here treated as distinct intervals;
        # truly equal intervals collapse to one canonical representative chosen
        # deterministically by mangle_type sort order).
        items = list(analysable.items())
        canonical: dict[RefinedType, RefinedType] = {}
        reps: list[RefinedType] = []
        for rt, iv in items:
            found = None
            for rep in reps:
                riv = analysable[rep]
                if interval_subset(iv, riv) and interval_subset(riv, iv):
                    found = rep
                    break
            if found is None:
                reps.append(rt)
                canonical[rt] = rt
            else:
                canonical[rt] = found

        # Deterministic ordering for representatives.
        reps.sort(key=mangle_type)

        # Build a forest over the containment partial order. Because
        # geneticengine only registers a node under its single ``mro()[1]``
        # base, each refined class gets exactly one parent: its *tightest
        # strictly-wider* representative (its immediate predecessor in the
        # subtype order), falling back to the base class when none exists.
        # Incomparable refinements become independent children of the base, so
        # we never force unrelated refinements into one artificial line.

        def strictly_contains(outer: RefinedType, inner: RefinedType) -> bool:
            """outer ⊋ inner: inner's values all satisfy outer, but not vice
            versa (so outer is strictly wider)."""
            return interval_subset(analysable[inner], analysable[outer]) and not interval_subset(
                analysable[outer], analysable[inner]
            )

        # Rank by how many reps strictly contain a node: widest first, so a
        # parent is always created before its children (no __bases__ mutation).
        def width_rank(rt: RefinedType) -> int:
            return sum(1 for other in reps if other is not rt and strictly_contains(other, rt))

        ordered = sorted(reps, key=lambda rt: (width_rank(rt), mangle_type(rt)))

        base_class: TypingType = data[base_type]
        new_classes: dict[RefinedType, TypingType] = {}
        for rt in ordered:
            # Immediate parent = tightest strictly-wider rep already created.
            parents = [p for p in ordered if p in new_classes and strictly_contains(p, rt)]
            if parents:
                # Tightest = the one whose interval is contained in all the
                # others (most-derived). Deterministic via the width_rank /
                # mangle_type ordering already applied to ``ordered``.
                parent_rt = max(
                    parents,
                    key=lambda p: (width_rank(p), mangle_type(p)),
                )
                parent_class = new_classes[parent_rt]
            else:
                parent_class = base_class
            cls = type(mangle_type(rt), (parent_class, ABC), {})
            cls = abstract(cls)
            new_classes[rt] = cls

        # Point every refined key (including collapsed equivalents) at its
        # canonical forest class.
        for rt in analysable:
            data[rt] = new_classes[canonical[rt]]


def create_literal_class(
    aeon_type: Type, parent_class: type, value_type: None | type | MetaHandlerGenerator = None
) -> type:
    """Create and return a new literal class with the given name and value type, based on the provided abstract class."""
    if value_type is None:
        value_type = aeon_to_python[aeon_type]

    class_name = mangle_type(aeon_type)
    new_class = make_dataclass(
        f"literal_{class_name}",
        [("value", value_type)],
        bases=(parent_class,),
    )

    def get_core(self):
        value = getattr(self, "value", None)
        return Literal(value, type=aeon_type)

    setattr(new_class, "get_core", get_core)
    new_class = weight(LITERAL_WEIGHT)(new_class)
    return new_class


def create_literals_nodes(type_info: dict[Type, TypingType], types: Optional[list[Type]] = None) -> list[TypingType]:
    """Creates all literal nodes for known types with literals (bool, int, float, string).

    For Int, the unlimited-range literal is replaced by a metahandler-based literal
    (IntRange(-1, 256)) to avoid the enumerative search iterating over hundreds of
    millions of values before finding valid ones.
    """
    if types is None:
        types = [t_bool, t_int, t_float, t_string]

    xname = Name("x", fresh_counter.fresh())

    gtm1 = LiquidApp(Name("<=", 0), [LiquidLiteralInt(-1), LiquidVar(xname)])
    lt256 = LiquidApp(Name("<=", 0), [LiquidVar(xname), LiquidLiteralInt(256)])
    base_int = create_literal_class(
        t_int,
        _get(type_info, t_int),
        refined_type_to_metahandler(RefinedType(xname, t_int, LiquidApp(Name("&&", 0), [gtm1, lt256]))),
    )

    # Exclude t_int from the unlimited-range list; use the metahandler-based base_int instead.
    types_without_unlimited_int = [ty for ty in types if ty != t_int]
    return [create_literal_class(aeon_ty, _get(type_info, aeon_ty)) for aeon_ty in types_without_unlimited_int] + [
        base_int
    ]


def create_literal_ref_nodes(type_info: dict[Type, TypingType] = None) -> list[TypingType]:
    """Creates literal nodes for refined types using metahandlers.

    Each node:
    - Uses a metahandler (e.g. IntRange(1, 99)) so the enumerative search only
      iterates values that satisfy the refinement.
    - Inherits from the refined type's grammar class, which itself chains down to
      the BASE type's class (e.g. æInt). This keeps it a (transitive) alternative
      of the base class while also letting wider refined classes reach narrower
      refined literals through the subtyping chain (issue #312).

    - Returns a Literal with the base (unrefined) type from get_core() so the
      type checker can handle it correctly.
    """
    ref_types = [ty for ty in type_info if isinstance(ty, RefinedType) and ty.type in aeon_to_python]
    result = []
    for aeon_ty in ref_types:
        base_type = aeon_ty.type
        # Parent is the refined type's class, which (after wire_refined_subtyping)
        # chains down through any wider refinements to the base class.
        parent_class = _get(type_info, aeon_ty)
        metahandler = refined_type_to_metahandler(aeon_ty)
        if metahandler is None:
            continue
        lit_class = create_literal_class(aeon_ty, parent_class, metahandler)

        def get_core(self, bt=base_type):
            value = getattr(self, "value", None)
            return Literal(value, type=bt)

        setattr(lit_class, "get_core", get_core)
        result.append(lit_class)
    return result


def create_var_node(name: Name, ty: Type, python_ty: TypingType) -> TypingType:
    """Creates a python type for a given variable in context."""
    vname = mangle_var(name)
    dc = make_dataclass(f"var_{vname}", [], bases=(python_ty,))

    def get_core(_):
        return Var(name)

    setattr(dc, "get_core", get_core)
    dc = weight(VAR_WEIGHT)(dc)
    return dc


def create_var_apps_node(name: Name, ty: AbstractionType, type_info: dict[Type, TypingType]) -> TypingType:
    """Creates a python type for a given variable in context that is a function."""

    # Collect arguments
    args: list[tuple[Name, Type]] = []
    current: Type = ty
    while isinstance(current, AbstractionType):
        args.append((current.var_name, current.var_type))
        current = current.type
    rtype = current
    # Normalize binder-dependent occurrences in the return type to `__self__`,
    # matching the storage convention used by `extract_all_types`.
    for aname, _ in args:
        rtype = substitution_in_type(rtype, Var(Name("__self__", 0)), aname)
    python_ty = _get(type_info, rtype)

    vname = mangle_var(name)
    dc = make_dataclass(
        f"var_app_{vname}", [(mangle_name(aname), _get(type_info, ty)) for (aname, ty) in args], bases=(python_ty,)
    )

    def get_core(_self):
        current = Var(name)
        for aname, _ in args:
            current = Application(current, getattr(_self, mangle_name(aname)).get_core())

        return current

    setattr(dc, "get_core", get_core)
    dc = weight(VAR_WEIGHT)(dc)
    return dc


def create_var_nodes(vars: list[Tuple[Name, Type]], type_info: dict[Type, TypingType]) -> list[TypingType]:
    """Creates a list of python types for all variables in context."""
    return [create_var_node(var_name, ty, _get(type_info, ty)) for (var_name, ty) in vars if _has(type_info, ty)] + [
        create_var_apps_node(var_name, ty, type_info)
        for (var_name, ty) in vars
        if _has(type_info, ty) and isinstance(ty, AbstractionType)
    ]


def create_abstraction_node(ty: AbstractionType, type_info: dict[Type, TypingType]) -> TypingType:
    """Creates a dataclass to represent an abstraction (\\_0 -> x) of type sth_arrow_X."""
    vname = f"lambda_{mangle_type(ty)}"
    return_type = substitution_in_type(ty.type, Var(Name("__self__", 0)), ty.var_name)
    dc = make_dataclass(vname, [("body", _get(type_info, return_type))], bases=(_get(type_info, ty),))

    def get_core(_self):
        return Annotation(Abstraction(Name("_0", fresh_counter.fresh()), _self.body.get_core()), ty)

    # Note: We cannot use the variable inside Abstraction.
    setattr(dc, "get_core", get_core)
    dc = weight(ABS_WEIGHT)(dc)
    return dc


def collect_all_abstractions(t: Type) -> Generator[AbstractionType]:
    match t:
        case RefinedType(_, _, _) | TypeConstructor(_) | TypeVar() | Top():
            return
        case AbstractionType(_, aty, rty):
            yield t
            yield from collect_all_abstractions(aty)
            yield from collect_all_abstractions(rty)
        case TypePolymorphism(_, _, body):
            yield from collect_all_abstractions(body)
        case _:
            assert False, f"Unsupported {t}"


def create_abstraction_nodes(type_info: dict[Type, TypingType]) -> list[TypingType]:
    return [
        create_abstraction_node(ity, type_info)
        for ty in type_info
        for ity in collect_all_abstractions(ty)
        if isinstance(ity, AbstractionType)
    ]


def create_application_node(ty: AbstractionType, type_info: dict[Type, TypingType]) -> TypingType:
    """Creates a dataclass to represent an abstraction (\\_0 -> x) of type sth_arrow_X."""
    vname = f"app_{mangle_type(ty)}"
    return_type = substitution_in_type(ty.type, Var(Name("__self__", 0)), ty.var_name)
    dc = make_dataclass(
        vname,
        [("fun", _get(type_info, ty)), ("arg", _get(type_info, ty.var_type))],
        bases=(_get(type_info, return_type),),
    )

    # Note: this would require dependent type dynamic processing on the return type (parent class)

    def get_core(_self):
        return Application(_self.fun.get_core(), _self.arg.get_core())

    setattr(dc, "get_core", get_core)
    dc = weight(APP_WEIGHT)(dc)
    return dc


def create_application_nodes(type_info: dict[Type, TypingType]) -> list[TypingType]:
    return [create_application_node(ty, type_info) for ty in type_info if isinstance(ty, AbstractionType)]


def create_if_node(ty: Type, type_info: dict[Type, TypingType]) -> TypingType:
    v_name = f"if_{mangle_type(ty)}"
    dc = make_dataclass(
        v_name,
        [("cond", _get(type_info, t_bool)), ("then", type_info[ty]), ("otherwise", type_info[ty])],
        bases=(type_info[ty],),
    )

    def get_core(_self):
        return Annotation(If(_self.cond.get_core(), _self.then.get_core(), _self.otherwise.get_core()), ty)

    setattr(dc, "get_core", get_core)
    dc = weight(IF_WEIGHT)(dc)
    return dc


def create_if_nodes(type_info: dict[Type, TypingType]) -> list[TypingType]:
    return [create_if_node(ty, type_info) for ty in type_info]


def filter_uninterpreted(lt: LiquidTerm) -> Optional[LiquidTerm]:
    match lt:
        case LiquidHole():
            return lt
        case (
            LiquidLiteralBool(_)
            | LiquidLiteralInt(_)
            | LiquidLiteralFloat(_)
            | LiquidLiteralString(_)
            | LiquidLiteralUnit()
            | LiquidVar(_)
        ):
            return lt
        case LiquidApp(fun, args):
            if fun in ["&&", "||"]:
                nargs = [filter_uninterpreted(x) for x in args]
                if nargs[0] is None:
                    return nargs[1]
                if nargs[1] is None:
                    return nargs[0]
                return LiquidApp(fun, nargs)
            elif fun in ops:
                nargs = [filter_uninterpreted(x) for x in args]
                if None not in nargs:
                    return LiquidApp(fun, nargs)
                else:
                    return None
            else:
                # user-defined uninterpreted function
                return None
        case _:
            assert False, f"Failed {lt}"


def remove_uninterpreted_functions_from_type(ty: Type) -> Type:
    match ty:
        case TypeConstructor(_, _) | TypeVar(_) | Top():
            return ty
        case AbstractionType(var_name, var_type, type):
            return AbstractionType(
                var_name,
                remove_uninterpreted_functions_from_type(var_type),
                remove_uninterpreted_functions_from_type(type),
            )
        case RefinedType(name, type, ref):
            ref_filtered = filter_uninterpreted(ref)
            if ref_filtered is None:
                return type
            else:
                return RefinedType(name, type, ref_filtered)
        case TypePolymorphism(name, kind, body):
            return TypePolymorphism(name, kind, remove_uninterpreted_functions_from_type(body))
        case RefinementPolymorphism(_, _, body):
            return remove_uninterpreted_functions_from_type(body)
        case _:
            assert False, f"Unsupported {ty}"


def remove_uninterpreted_functions_wrap(e: TypingContextEntry) -> TypingContextEntry:
    match e:
        case VariableBinder(name, type):
            type = remove_uninterpreted_functions_from_type(type)
            return VariableBinder(name, type)
        case UninterpretedBinder(_, _) | TypeBinder(_, _) | TypeConstructorBinder(_, _):
            return e
        case _:
            assert False, f"Unsupported {e}"


def remove_uninterpreted_functions(ctx: TypingContext) -> TypingContext:
    return TypingContext([remove_uninterpreted_functions_wrap(el) for el in ctx.entries])


def propagate_constants(ctx: TypingContext) -> tuple[TypingContext, dict[Name, LiquidTerm]]:
    substitutions: dict[Name, LiquidTerm] = {}
    entries: list[TypingContextEntry] = []
    for e in ctx.entries:
        match e:
            case VariableBinder(name, ty):
                # Apply all pending substitions

                for k in substitutions:
                    ty = substitution_liquid_in_type(ty, substitutions[k], k)

                # Detect the pattern {n:T | n == C}
                match ty:
                    case RefinedType(rname, _, LiquidApp(Name("==", _), [LiquidVar(iname), val])):
                        if rname == iname:
                            substitutions[rname] = val
                entries.append(VariableBinder(name, ty))
            case _:
                entries.append(e)

    return TypingContext(entries), substitutions


def _collect_tcs(ty: Type, result: set[TypeConstructor]):
    """Recursively collect all TypeConstructor instances from a type."""
    match ty:
        case TypeConstructor(_, args):
            result.add(ty)
            for arg in args:
                _collect_tcs(arg, result)
        case RefinedType(_, inner, _):
            _collect_tcs(inner, result)
        case AbstractionType(_, var_type, ret_type):
            _collect_tcs(var_type, result)
            _collect_tcs(ret_type, result)
        case TypePolymorphism(_, _, body):
            _collect_tcs(body, result)
        case RefinementPolymorphism(_, sort, body):
            _collect_tcs(sort, result)
            _collect_tcs(body, result)
        case _:
            pass


def _collect_type_arg_types(ty: Type, result: set[TypeConstructor]):
    """Collect types used as arguments to parameterized TypeConstructors."""
    match ty:
        case TypeConstructor(_, args):
            for arg in args:
                if isinstance(arg, TypeConstructor):
                    result.add(arg)
                _collect_type_arg_types(arg, result)
        case RefinedType(_, inner, _):
            _collect_type_arg_types(inner, result)
        case AbstractionType(_, var_type, ret_type):
            _collect_type_arg_types(var_type, result)
            _collect_type_arg_types(ret_type, result)
        case TypePolymorphism(_, _, body):
            _collect_type_arg_types(body, result)
        case _:
            pass


def monomorphize_poly_type(
    ty: TypePolymorphism,
    instantiation_types: set[TypeConstructor],
) -> list[tuple[Type, list[Type]]]:
    """Monomorphize a polymorphic type by instantiating forall-bound vars with candidate types.

    Args:
        ty: The polymorphic type to monomorphize.
        instantiation_types: Types to use for instantiation (should be non-parametric types
            that actually appear as type arguments in the program).

    Returns list of (monomorphized_body, type_applications) pairs.
    """
    foralls: list[Name] = []
    current: Type = ty
    while isinstance(current, TypePolymorphism):
        foralls.append(current.name)
        current = current.body

    # Skip types with RefinementPolymorphism (e.g. $)
    if isinstance(current, RefinementPolymorphism):
        return []

    # Sorted for reproducibility (set iteration order is id-dependent).
    base_types = sorted(instantiation_types, key=repr)
    if not base_types:
        return []

    results = []
    for combo in product(base_types, repeat=len(foralls)):
        body = current
        type_apps: list[Type] = list(combo)
        for tvar_name, concrete_ty in zip(foralls, combo):
            body = substitute_vartype(body, concrete_ty, tvar_name)
        results.append((body, type_apps))

    return results


def create_monomorphized_var_nodes(
    monomorphized: list[tuple[Name, Type, list[Type]]],
    type_info: dict[Type, TypingType],
) -> list[TypingType]:
    """Create grammar nodes for monomorphized polymorphic variables."""
    nodes: list[TypingType] = []
    for name, mono_ty, type_apps in monomorphized:
        # Simple var node (produces the type-applied function/value)
        if _has(type_info, mono_ty):
            vname = mangle_var(name) + "_mono_" + "_".join(mangle_type(t) for t in type_apps)
            dc = make_dataclass(f"var_{vname}", [], bases=(_get(type_info, mono_ty),))

            def get_core(_, _name=name, _ta=type_apps):
                term = Var(_name)
                for t in _ta:
                    term = TypeApplication(term, t)
                return term

            setattr(dc, "get_core", get_core)
            dc = weight(VAR_WEIGHT)(dc)
            nodes.append(dc)

        # Fully-applied function node
        if isinstance(mono_ty, AbstractionType):
            args: list[tuple[Name, Type]] = []
            current: Type = mono_ty
            while isinstance(current, AbstractionType):
                args.append((current.var_name, current.var_type))
                current = current.type
            rtype = current
            # Normalize binder-dependent occurrences to `__self__`, matching the
            # storage convention used by `extract_all_types`.
            for aname, _ in args:
                rtype = substitution_in_type(rtype, Var(Name("__self__", 0)), aname)

            if not _has(type_info, rtype) or any(not _has(type_info, aty) for _, aty in args):
                continue

            vname = mangle_var(name) + "_mono_" + "_".join(mangle_type(t) for t in type_apps)
            dc = make_dataclass(
                f"var_app_{vname}",
                [(mangle_name(aname), _get(type_info, aty)) for (aname, aty) in args],
                bases=(_get(type_info, rtype),),
            )

            args_names = [aname for aname, _ in args]

            def get_core_app(_self, _name=name, _ta=type_apps, _args=args_names):
                term = Var(_name)
                for t in _ta:
                    term = TypeApplication(term, t)
                for aname in _args:
                    term = Application(term, getattr(_self, mangle_name(aname)).get_core())
                return term

            setattr(dc, "get_core", get_core_app)
            dc = weight(APP_WEIGHT)(dc)
            nodes.append(dc)

    return nodes


def gen_grammar_nodes(
    ctx: TypingContext,
    ty: Type,
    synth_func_name: Name,
    metadata: Metadata,
    grammar_nodes: list[type] | None = None,
    start_override: Type | None = None,
) -> tuple[list[type], type]:
    """Generate grammar nodes from the variables in the given TypingContext.

    This function iterates over the variables in the provided TypingContext. For each variable,
    it generates a new class using the create_class_from_ctx_var function and adds it to
    the list of grammar_nodes. If no initial list of grammar_nodes is provided, it starts with an empty list.

    Args:
        ctx (TypingContext): The TypingContext to extract variables from.
        synth_func_name (str) : The name of the function where the hole is located
        metadata (Metadata): The metadata of the program.
        grammar_nodes (list[type]): Initial list of grammar nodes. Defaults to an empty list.

    Returns:
        list[type]: The list of generated grammar nodes.
    """
    if grammar_nodes is None:
        grammar_nodes = []

    # Clean context to remove non-interpreted functions from the context.
    # Simple refinements like 0 < n && n < 10 are kept.
    ctx, _ = propagate_constants(ctx)
    ctx = remove_uninterpreted_functions(ctx)
    ty = remove_uninterpreted_functions_from_type(ty)

    current_metadata = metadata.get(synth_func_name, {})
    is_recursion_allowed = current_metadata.get("recursion", False)
    vars_to_ignore = current_metadata.get("hide", [])
    vars_to_ignore_names = {v.name for v in vars_to_ignore}
    types_to_ignore = current_metadata.get("hide_types", [])

    def skip(name: Name) -> bool:
        if name == synth_func_name:
            return not is_recursion_allowed
        elif name.name in vars_to_ignore_names:
            return True
        elif name.name.startswith("__internal__"):
            return True
        elif name.name in ["native", "native_import", "print"]:
            return True
        else:
            return False

    ctx_vars = [(var_name, ty) for (var_name, ty) in ctx.concrete_vars() if not skip(var_name)]

    # Separate polymorphic and monomorphic context variables
    poly_ctx_vars = [(vn, vt) for (vn, vt) in ctx_vars if isinstance(vt, TypePolymorphism)]
    mono_ctx_vars = [(vn, vt) for (vn, vt) in ctx_vars if not isinstance(vt, TypePolymorphism)]

    # Strip refinements from the return positions of monomorphic variable
    # types but keep them on argument positions so the grammar can sample
    # values within each argument's refinement bounds.
    ctx_vars_unrefined = [
        (var_name, strip_refinements_keep_arg_refinements(var_ty)) for (var_name, var_ty) in mono_ctx_vars
    ]

    # Collect types that are used as type arguments to parameterized constructors.
    # These are the only types we need to instantiate forall-bound variables with.
    # For example, in `List Chunk`, `Chunk` is a type argument.
    instantiation_types: set[TypeConstructor] = set()
    for _, vt in mono_ctx_vars:
        _collect_type_arg_types(vt, instantiation_types)
    _collect_type_arg_types(ty, instantiation_types)

    # Monomorphize polymorphic variables. Arithmetic operators (`+ - * / %`)
    # are declared `forall a:B, a -> a -> a` in the prelude but only make
    # sense for numeric sorts — z3 has no `*` over uninterpreted constructor
    # sorts, so a candidate like `Chunk + Chunk` crashes verification.
    # Restrict their instantiation set to numeric types.
    numeric_arith_ops = {"+", "-", "*", "/", "%"}
    numeric_only_types: set[TypeConstructor] = {t for t in instantiation_types if t in (t_int, t_float)} or {
        t_int,
        t_float,
    }
    monomorphized: list[tuple[Name, Type, list[Type]]] = []
    for vn, vt in poly_ctx_vars:
        inst_types = numeric_only_types if vn.name in numeric_arith_ops else instantiation_types
        for mono_body, type_apps in monomorphize_poly_type(vt, inst_types):
            mono_body_unrefined = strip_refinements_keep_arg_refinements(mono_body)
            monomorphized.append((vn, mono_body_unrefined, type_apps))

    # Collect types from monomorphized vars
    mono_extra_types: set[Type] = set()
    for _, mt, _ in monomorphized:
        mono_extra_types.add(mt)

    # Build set of all types to consider
    types_to_consider = (
        set([t_bool, t_float, t_int, t_string]) | set([x[1] for x in ctx_vars_unrefined]) | set([ty]) | mono_extra_types
    )
    if start_override is not None:
        types_to_consider = types_to_consider | {start_override}
    types_to_consider = types_to_consider - set(TypeConstructor(t) for t in types_to_ignore)
    # Sort by a stable string key so grammar construction is reproducible across
    # processes: ``set`` iteration order over types / node classes otherwise
    # depends on object ``id()`` (and hence allocation order), which makes
    # seeded generation non-deterministic between runs.
    type_info = extract_all_types(sorted(types_to_consider, key=repr), ctx, instantiation_types)
    type_nodes = sorted(set(type_info.values()), key=lambda c: c.__name__)

    literals = create_literals_nodes(type_info)
    vars = create_var_nodes(ctx_vars_unrefined, type_info)
    abstractions = create_abstraction_nodes(type_info)
    applications = create_application_nodes(type_info)
    literals_ref = create_literal_ref_nodes(type_info)
    ifs = create_if_nodes(type_info)
    mono_nodes = create_monomorphized_var_nodes(monomorphized, type_info)

    ret = type_nodes + literals + literals_ref + vars + applications + abstractions + mono_nodes
    if mangle_name(synth_func_name) in metadata and "disable_control_flow" in metadata[synth_func_name]:
        ret = ret + ifs
    # Use the unrefined base type as the grammar starting node.
    # Refined type metahandler literals are direct alternatives for the base class,
    # so no refined abstract class is needed as a starting symbol.
    # `refined_to_unrefined_type` does not peel TypePolymorphism, and we never
    # register the forall node itself, so for a polymorphic synthesis target we
    # derive the starting node from its first monomorphized body.
    # TODO: synthesize across all instantiations of a polymorphic target.
    if start_override is not None:
        # Property-based testing starts generation from a refined node so the
        # metahandler enforces the refinement at generation time (no discards),
        # instead of the unrefined base used for synthesis (which relies on a
        # separate validator). The refined node's only alternatives are
        # in-range literals, so this also avoids generating arbitrary
        # value-producing expressions.
        start_ty = start_override
    elif isinstance(ty, TypePolymorphism):
        mono = monomorphize_poly_type(ty, instantiation_types)
        start_ty = refined_to_unrefined_type(mono[0][0]) if mono else refined_to_unrefined_type(ty)
    else:
        start_ty = refined_to_unrefined_type(ty)
    return ret, _get(type_info, start_ty)


def print_grammar_nodes_names(grammar_nodes: list[type]) -> None:
    class_names = [cls.__name__ for cls in grammar_nodes]
    print(class_names)


def print_grammar_nodes(grammar_nodes: list[type]) -> None:
    for cls in grammar_nodes:
        parents = [base.__name__ for base in cls.__bases__]
        print("@dataclass")
        print(f"class {cls.__name__}({', '.join(parents)}):")
        class_vars = cls.__annotations__
        if class_vars:
            for var_name, var_type in class_vars.items():
                print(f"\t {var_name}: {str(var_type)}")
        else:
            print("\t pass")
        print()
        # print("---------------------------------------------------")


def _determinize_grammar(g: Grammar) -> Grammar:
    """Sort a grammar's productions and their alternatives by class name so the
    seed -> choice mapping is reproducible across processes.

    ``Grammar.usable_grammar`` rebuilds the grammar from a ``set`` of reachable
    symbols (``list(set(...))``), whose order depends on object ``id()`` and thus
    on allocation order. Sampling chooses among ``alternatives[symbol]``, so
    making that ordering deterministic is sufficient for reproducible generation.
    Weights are stored per production class, so reordering does not change them."""
    g.alternatives = {
        key: sorted(g.alternatives[key], key=lambda c: c.__name__)
        for key in sorted(g.alternatives, key=lambda c: c.__name__)
    }
    return g


def create_grammar(
    ctx: TypingContext,
    ty: Type,
    fun_name: Name,
    metadata: Metadata,
    start_override: Type | None = None,
) -> Grammar:
    grammar_nodes, starting_node = gen_grammar_nodes(ctx, ty, fun_name, metadata, [], start_override=start_override)
    g = extract_grammar(grammar_nodes, starting_node)
    g = g.usable_grammar()
    return _determinize_grammar(g)
