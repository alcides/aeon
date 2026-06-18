"""Random ``Term`` generation for property-based testing.

This is a thin wrapper around the synthesis grammar machinery
(:func:`aeon.synthesis.grammar.grammar_generation.create_grammar` +
geneticengine's tree representation). The same code that turns a ``Type`` into a
search space for program synthesis is reused here to turn a ``Type`` into a
sampler of random inhabitants — so refinements (via metahandlers) constrain the
generated values automatically and users never write their own generators.
"""

from __future__ import annotations

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.terms import Term
from aeon.core.types import RefinedType, Type, TypeConstructor, t_bool, t_float, t_int, t_string
from aeon.decorators.api import Metadata
from aeon.synthesis.grammar.grammar_generation import create_grammar
from aeon.typechecking.context import TypeBinder, TypeConstructorBinder, TypingContext, VariableBinder
from aeon.utils.name import Name

from geneticengine.random.sources import NativeRandomSource
from geneticengine.representations.tree.initializations import MaxDepthDecider
from geneticengine.representations.tree.treebased import TreeBasedRepresentation

# Mirrors the depth used by the GP synthesizer (``ge_synthesis.py``).
DEFAULT_MAX_DEPTH = 5

# Base types for which generation can start from a (possibly trivial) refined
# node, yielding clean in-range literals rather than arbitrary expressions.
_BASE_TYPES = (t_int, t_float, t_bool, t_string)


def is_base_type(ty: Type) -> bool:
    """Whether ``ty`` is a base type (or a refinement of one), as opposed to a
    user-defined algebraic datatype like ``List`` or ``Maybe``."""
    if isinstance(ty, RefinedType):
        return ty.type in _BASE_TYPES
    return isinstance(ty, TypeConstructor) and ty in _BASE_TYPES


def build_adt_context(typing_ctx: TypingContext, constructor_binders: list[VariableBinder]) -> TypingContext:
    """A generation context for algebraic datatypes containing ONLY data
    constructors (plus the type/type-constructor declarations needed to resolve
    them). Ordinary functions are dropped so generation yields pure constructor
    trees instead of arbitrary value-producing expressions.

    Constructors carry an abstract refinement (``forall <p:a->Bool>``) that
    ``monomorphize_poly_type`` cannot instantiate; ``create_grammar`` strips it
    via ``remove_uninterpreted_functions`` before monomorphizing, so the cleaned
    constructor becomes a usable polymorphic node."""
    keep = [e for e in typing_ctx.entries if isinstance(e, (TypeConstructorBinder, TypeBinder))]
    return TypingContext(keep + list(constructor_binders))


def _refined_start(ty: Type) -> Type | None:
    """Return the refined node to start generation from for a base-typed target,
    or ``None`` when the type is not a base type (e.g. an ADT like ``List``).

    A plain base type ``B`` is treated as ``{v:B | true}`` so generation still
    starts from a refined literal node — producing clean literals instead of
    value-producing expressions. A refined base type is used as-is, so its
    metahandler constrains the draws to the refinement (no discards)."""
    if isinstance(ty, RefinedType) and ty.type in _BASE_TYPES:
        return ty
    if isinstance(ty, TypeConstructor) and ty in _BASE_TYPES:
        return RefinedType(Name("v", 0), ty, LiquidLiteralBool(True))
    return None


class TypeSampler:
    """Samples random ``Term``s of a fixed ``Type`` in a fixed context.

    Building the grammar is the expensive step, so it is done once per
    ``(ctx, ty)`` and reused across draws. For dependent arguments — where the
    type changes once an earlier argument has been chosen — build a fresh
    sampler per draw via :func:`generate_one`.
    """

    def __init__(
        self,
        ctx: TypingContext,
        ty: Type,
        fun_name: Name,
        metadata: Metadata,
        seed: int = 0,
        max_depth: int = DEFAULT_MAX_DEPTH,
    ):
        self.random = NativeRandomSource(seed)
        grammar = create_grammar(ctx, ty, fun_name, metadata, start_override=_refined_start(ty))
        self.representation = TreeBasedRepresentation(
            grammar,
            decider=MaxDepthDecider(self.random, grammar, max_depth=max_depth),
        )

    def sample(self) -> Term:
        genotype = self.representation.create_genotype(self.random)
        phenotype = self.representation.genotype_to_phenotype(genotype)
        term = phenotype.get_core()
        assert isinstance(term, Term)
        return term


def generate_one(
    ctx: TypingContext,
    ty: Type,
    fun_name: Name,
    metadata: Metadata,
    seed: int = 0,
    max_depth: int = DEFAULT_MAX_DEPTH,
) -> Term:
    """Generate a single random ``Term`` inhabiting ``ty`` under ``ctx``.

    A new grammar is built each call, so this is the right entry point when the
    target type depends on previously chosen arguments. For many independent
    draws of the *same* type, instantiate a :class:`TypeSampler` and call
    :meth:`TypeSampler.sample` repeatedly.
    """
    return TypeSampler(ctx, ty, fun_name, metadata, seed=seed, max_depth=max_depth).sample()
