"""Random ``Term`` generation for property-based testing.

Uses the same native grammar random walks as ``-s random_search``: typed holes
are expanded with Aeon's backward/forward actions (and SMT leaf completion for
refinements), so inhabitants respect refinements without a GeneticEngine grammar.
"""

from __future__ import annotations

import random

from aeon.core.terms import Term
from aeon.core.types import RefinedType, Type, TypeConstructor, t_bool, t_float, t_int, t_string
from aeon.decorators.api import Metadata
from aeon.synthesis.modules.native_search import MAX_DEPTH, initial_partial, make_skip, sample_one
from aeon.typechecking.context import (
    TypeBinder,
    TypeConstructorBinder,
    TypingContext,
    TypingContextEntry,
    VariableBinder,
)
from aeon.utils.name import Name

DEFAULT_MAX_DEPTH = MAX_DEPTH
_SAMPLE_ATTEMPTS = 64

_BASE_TYPES = (t_int, t_float, t_bool, t_string)


def is_base_type(ty: Type) -> bool:
    """Whether ``ty`` is a base type (or a refinement of one), as opposed to a
    user-defined algebraic datatype like ``List`` or ``Maybe``."""
    if isinstance(ty, RefinedType):
        return ty.type in _BASE_TYPES
    return isinstance(ty, TypeConstructor) and ty in _BASE_TYPES


def build_base_context() -> TypingContext:
    """Minimal context for sampling base (or refined-base) values.

    Full program contexts (e.g. after ``open List`` / ``open Testing``) expose
    hundreds of Instantiable functions; monomorphizing them for an ``Int`` hole
    makes type-directed walks time out or never close. Built-ins alone suffice:
    unrefined bases become literals, and refinements are discharged by SMT after
    dependent arguments have been substituted into the type.
    """
    return TypingContext([])


def build_adt_context(typing_ctx: TypingContext, constructor_binders: list[VariableBinder]) -> TypingContext:
    """A generation context for algebraic datatypes containing ONLY data
    constructors (plus the type/type-constructor declarations needed to resolve
    them). Ordinary functions are dropped so generation yields pure constructor
    trees instead of arbitrary value-producing expressions.

    Abstract refinements (``forall <p>``) are kept on constructors —
    ``monomorphize`` opens them with an ``ImplicitRefinementHole`` so Horn
    inference can instantiate ``p``. Liquid atoms that mention uninterpreted
    measures (e.g. ``List_size``) are erased so SMT subtyping does not need
    those binders in the narrowed ADT context.
    """
    from aeon.synthesis.grammar.poly import remove_uninterpreted_functions_from_type

    keep: list[TypingContextEntry] = [
        e for e in typing_ctx.entries if isinstance(e, (TypeConstructorBinder, TypeBinder))
    ]
    cleaned: list[TypingContextEntry] = [
        VariableBinder(b.name, remove_uninterpreted_functions_from_type(b.type)) for b in constructor_binders
    ]
    return TypingContext(keep + cleaned)


class TypeSampler:
    """Samples random ``Term``s of a fixed ``Type`` in a fixed context.

    The initial partial AST and skip function are built once; each
    :meth:`sample` runs an independent random walk (advancing the RNG).
    For dependent arguments — where the type changes once an earlier argument
    has been chosen — build a fresh sampler per draw via :func:`generate_one`.
    """

    def __init__(
        self,
        ctx: TypingContext,
        ty: Type,
        fun_name: Name,
        metadata: Metadata,
        seed: int = 0,
        max_depth: int = DEFAULT_MAX_DEPTH,
        prefer_closed: bool | None = None,
    ):
        self.rng = random.Random(seed)
        self.initial = initial_partial(ctx, ty)
        self.skip = make_skip(fun_name, metadata)
        self.max_depth = max_depth
        # Prefer terminals for base types; explore recursive constructors for ADTs.
        self.prefer_closed = is_base_type(ty) if prefer_closed is None else prefer_closed

    def sample(self) -> Term:
        # Always allow a closed-terminal fallback so ADT walks that starve
        # recursion still finish with a nullary constructor (e.g. ``List_nil``).
        prefer_order = (self.prefer_closed,) if self.prefer_closed else (False, True)
        for prefer_closed in prefer_order:
            for _ in range(_SAMPLE_ATTEMPTS):
                term = sample_one(
                    self.initial,
                    self.skip,
                    self.rng,
                    self.max_depth,
                    prefer_closed=prefer_closed,
                )
                if term is not None:
                    return term
        raise RuntimeError(f"PBT TypeSampler failed to produce a term within {_SAMPLE_ATTEMPTS} attempts")


def generate_one(
    ctx: TypingContext,
    ty: Type,
    fun_name: Name,
    metadata: Metadata,
    seed: int = 0,
    max_depth: int = DEFAULT_MAX_DEPTH,
) -> Term:
    """Generate a single random ``Term`` inhabiting ``ty`` under ``ctx``.

    A new sampler is built each call, so this is the right entry point when the
    target type depends on previously chosen arguments. For many independent
    draws of the *same* type, instantiate a :class:`TypeSampler` and call
    :meth:`TypeSampler.sample` repeatedly.
    """
    return TypeSampler(ctx, ty, fun_name, metadata, seed=seed, max_depth=max_depth).sample()
