"""Synthesis-backed ``Term`` generation for property-based testing.

Supports native random walks, native enumeration, and TDSyn variants. Every
completed proposal passes Aeon's regular typechecker before it becomes an input.
"""

from __future__ import annotations

import random
from collections.abc import Iterator, Sequence

from aeon.core.terms import Term
from aeon.core.types import RefinedType, Type, TypeConstructor, t_bool, t_float, t_int, t_string
from aeon.decorators.api import Metadata
from aeon.synthesis.modules.native_search import MAX_DEPTH, initial_partial, make_skip, sample_one
from aeon.synthesis.identification import get_holes
from aeon.synthesis.pbt.backends import INPUT_SYNTHESIZERS, input_candidates
from aeon.typechecking.context import (
    TypingContext,
    UninterpretedBinder,
    VariableBinder,
)
from aeon.typechecking.typeinfer import check_type
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


def build_adt_context(typing_ctx: TypingContext, value_binders: list[VariableBinder]) -> TypingContext:
    """Expose the full program context to ADT input synthesis.

    Top-level core definitions are not necessarily in ``typing_ctx``. Add their
    bindings so ordinary functions and values, as well as constructors, can be
    used to generate inputs. Keep measure bindings and refinements unchanged.
    """
    entries = list(typing_ctx.entries)
    known = {entry.name for entry in entries if isinstance(entry, VariableBinder)}
    entries.extend(binder for binder in value_binders if binder.name not in known)
    return TypingContext(entries, trusted_names=typing_ctx.trusted_names)


class TypeSampler:
    """Samples checked ``Term``s of a fixed ``Type`` in a fixed context.

    The initial partial AST and skip function are built once; each
    :meth:`sample` advances the selected backend's walk or candidate stream.
    Multiple backends rotate round-robin; ``backend_counts`` records accepted
    inputs from each. Enumeration does not restart at the first solution.
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
        validation_ctx: TypingContext | None = None,
        synthesizers: str | Sequence[str] = ("random_search",),
    ):
        self.rng = random.Random(seed)
        self.type = ty
        self.synthesizers = (synthesizers,) if isinstance(synthesizers, str) else tuple(synthesizers)
        if not self.synthesizers or any(name not in INPUT_SYNTHESIZERS for name in self.synthesizers):
            raise ValueError(f"Unsupported PBT input synthesizers: {self.synthesizers}")
        self._backend_index = 0
        self.backend_counts = dict.fromkeys(self.synthesizers, 0)
        self._streams: dict[str, Iterator[Term | None]] = {}
        self._fun_name = fun_name
        self._metadata = metadata
        self._seed = seed
        # Component libraries cache the skip policy by context identity. Give
        # each sampler its own context because different properties have
        # different self-reference exclusions.
        ctx = TypingContext(list(ctx.entries), trusted_names=ctx.trusted_names)
        self._ctx = ctx
        self.validation_ctx = ctx if validation_ctx is None else validation_ctx
        self.initial = initial_partial(ctx, ty)
        skip = make_skip(fun_name, metadata)
        executable = {entry.name for entry in ctx.entries if isinstance(entry, VariableBinder)}
        logical_only = {
            entry.name
            for entry in ctx.entries
            if isinstance(entry, UninterpretedBinder) and entry.name not in executable
        }
        # Keep logical declarations for SMT, but do not call declarations with
        # no runtime implementation when constructing an executable input.
        self.skip = lambda name: name in logical_only or skip(name)
        self.max_depth = max_depth
        # Prefer terminals for base types; explore recursive constructors for ADTs.
        self.prefer_closed = is_base_type(ty) if prefer_closed is None else prefer_closed

    def sample(self, synthesizer: str | None = None) -> Term:
        backend = synthesizer or self.synthesizers[self._backend_index % len(self.synthesizers)]
        if backend not in self.synthesizers:
            raise ValueError(f"PBT input synthesizer {backend} is not configured on this sampler")
        self._backend_index += 1
        # Always allow a closed-terminal fallback so ADT walks that starve
        # recursion still finish with a nullary constructor (e.g. ``List_nil``).
        prefer_order = (self.prefer_closed,) if self.prefer_closed else (False, True)
        validation_error: Exception | None = None
        for prefer_closed in prefer_order:
            for _ in range(_SAMPLE_ATTEMPTS):
                if backend == "random_search":
                    term = sample_one(
                        self.initial,
                        self.skip,
                        self.rng,
                        self.max_depth,
                        prefer_closed=prefer_closed,
                    )
                else:
                    if backend not in self._streams:
                        self._streams[backend] = input_candidates(
                            backend,
                            self._ctx,
                            self.type,
                            self._fun_name,
                            self._metadata,
                            self.skip,
                            self._seed,
                            self.max_depth,
                        )
                    try:
                        term = next(self._streams[backend])
                    except StopIteration:
                        raise RuntimeError(f"PBT {backend} exhausted its bounded candidate stream for {self.type}")
                    except Exception as error:
                        raise RuntimeError(f"PBT {backend} input search failed: {error}") from error
                if term is not None and get_holes(term):
                    continue
                if term is not None:
                    # Grammar expansions and SMT leaf completion are proposals,
                    # not proofs. Check the entire expression, including every
                    # constructor argument and the specialised target type.
                    try:
                        valid = check_type(self.validation_ctx, term, self.type)
                    except Exception as error:
                        # Unsupported verification must never admit a candidate.
                        validation_error = error
                        continue
                    if not valid:
                        continue
                    self.backend_counts[backend] += 1
                    return term
        attempts = _SAMPLE_ATTEMPTS * len(prefer_order)
        message = f"PBT TypeSampler ({backend}) failed to produce a term within {attempts} attempts"
        if validation_error is not None:
            message += f"; validation raised {type(validation_error).__name__}: {validation_error}"
        raise RuntimeError(message) from validation_error


def generate_one(
    ctx: TypingContext,
    ty: Type,
    fun_name: Name,
    metadata: Metadata,
    seed: int = 0,
    max_depth: int = DEFAULT_MAX_DEPTH,
    synthesizers: str | Sequence[str] = ("random_search",),
) -> Term:
    """Generate a single random ``Term`` inhabiting ``ty`` under ``ctx``.

    A new sampler is built each call, so this is the right entry point when the
    target type depends on previously chosen arguments. For many independent
    draws of the *same* type, instantiate a :class:`TypeSampler` and call
    :meth:`TypeSampler.sample` repeatedly.
    """
    return TypeSampler(ctx, ty, fun_name, metadata, seed=seed, max_depth=max_depth, synthesizers=synthesizers).sample()
