"""Opt-in type-constrained local LLM synthesis (issue #648)."""

from __future__ import annotations

from dataclasses import fields, is_dataclass
import os
import random
from time import monotonic
from typing import Callable

from lark.exceptions import LarkError

from aeon.core.multiplicity import MOmega
from aeon.core.terms import Annotation, Let, Rec, Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.errors import AeonError
from aeon.synthesis.api import InvalidIndividualException, SynthesisNotSuccessful, Synthesizer, UnsupportedSynthesisGoal
from aeon.synthesis.identification import get_holes, term_has_holes
from aeon.synthesis.modules.type_constrained.prefix import Limits, PrefixEngine
from aeon.synthesis.modules.type_constrained.sampling import (
    DecodingExhausted,
    Sampling,
    Statistics,
    TokenAdapter,
    check_deadline,
    decode,
)
from aeon.synthesis.modules.type_constrained.types import Scope, ordinary
from aeon.synthesis.pareto import ParetoEntry, minimize_flags_from_goals, pick_pareto_member, update_pareto_front
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def check_program_scope(term: Term, metadata: Metadata) -> None:
    """The per-hole context does not encode local binder multiplicities.

    Check the path to the hole before dispatch, while declarations still carry
    that information. Independent/mutual multi-hole programs are not supported.
    """
    # The compiler's synthetic ?main continuation is not a synthesis target.
    if len({name for name in get_holes(term) if name != Name("main", 0)}) != 1:
        raise UnsupportedSynthesisGoal("llm_type_constrained currently requires exactly one program hole")

    def visit(node: Term) -> None:
        if not term_has_holes(node):
            return
        if isinstance(node, Annotation):
            ordinary(node.type)
        if isinstance(node, Rec) and term_has_holes(node.var_value):
            ordinary(node.var_type)
        if isinstance(node, (Let, Rec)) and term_has_holes(node.body) and node.multiplicity is not MOmega:
            raise UnsupportedSynthesisGoal("llm_type_constrained cannot capture linear/erased local binders")
        if not is_dataclass(node):
            raise UnsupportedSynthesisGoal(f"unsupported term in type-constrained scope: {type(node).__name__}")
        for field in fields(node):
            child = getattr(node, field.name)
            if isinstance(child, Term):
                visit(child)

    visit(term)


class TypeConstrainedSynthesizer(Synthesizer):
    def __init__(self, seed: int = 0, adapter_factory: Callable[[], TokenAdapter] | None = None):
        self.seed = seed
        self.adapter_factory = adapter_factory
        self.statistics = Statistics()

    def _adapter(self) -> TokenAdapter:
        if self.adapter_factory is not None:
            return self.adapter_factory()
        provider = os.environ.get("AEON_TC_PROVIDER", "transformers")
        if provider != "transformers":
            raise UnsupportedSynthesisGoal(
                f"{provider} has no token enforcement adapter; set AEON_TC_PROVIDER=transformers (no fallback)"
            )
        model = os.environ.get("AEON_TC_MODEL")
        if not model:
            raise UnsupportedSynthesisGoal("set AEON_TC_MODEL to a local Transformers model directory or model ID")
        from aeon.synthesis.modules.type_constrained.transformers_adapter import TransformersAdapter

        return TransformersAdapter.load(model, os.environ.get("AEON_TC_DEVICE", "cpu"))

    def synthesize(
        self,
        ctx: TypingContext,
        type: Type,
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        fun_name: Name,
        metadata: Metadata,
        budget: float = 60,
        ui: SynthesisUI = SynthesisUI(),
        output_value: Callable[[Term], object] | None = None,
    ) -> Term:
        started = monotonic()
        deadline = started + budget
        check_deadline(deadline, lambda: False)
        current = metadata.get(fun_name, {})
        if current.get("recursion", False):
            raise UnsupportedSynthesisGoal("llm_type_constrained does not support recursive synthesis")
        scope = Scope(ctx, type, fun_name, metadata)
        try:
            limits = Limits(max_states=int(os.environ.get("AEON_TC_MAX_STATES", "20000")))
            settings = Sampling(
                max_tokens=int(os.environ.get("AEON_TC_MAX_TOKENS", "128")),
                max_probes=int(os.environ.get("AEON_TC_MAX_PROBES", "4096")),
                initial_top_k=int(os.environ.get("AEON_TC_TOP_K", "32")),
                temperature=float(os.environ.get("AEON_TC_TEMPERATURE", "0")),
            )
            attempts = int(os.environ.get("AEON_TC_ATTEMPTS", "8"))
            if attempts <= 0:
                raise ValueError("AEON_TC_ATTEMPTS must be positive")
        except ValueError as error:
            raise UnsupportedSynthesisGoal(f"invalid type-constrained decoding configuration: {error}") from error
        engine = PrefixEngine(scope, limits)
        self.statistics = Statistics()
        rng = random.Random(self.seed)
        adapter = self._adapter()
        check_deadline(deadline, lambda: False)
        variables = ", ".join(f"{name}: {ty}" for name, (_, ty) in scope.bindings.items())
        examples = "\n".join(example.text for example in current.get("examples", []))
        prompt = (
            "Complete one Aeon expression, then EOS. No markdown or explanation. "
            "Syntax: f x, fun x => body, if condition then a else b, let x := value in body. "
            "Use = for equality. Parenthesize compound arguments.\n"
            f"Required type (including refinements): {type}\nIn-scope components: {variables}\n"
            f"Examples from the source program:\n{examples}\n"
            f"Task: {current.get('prompt', 'Satisfy the type and examples.')}\nExpression:\n"
        )
        minimize = minimize_flags_from_goals(current.get("goals", []))
        front: list[ParetoEntry] = []
        for _ in range(attempts):
            try:
                check_deadline(deadline, lambda: False)
                self.statistics.attempts += 1
                source = decode(adapter, engine, prompt, deadline, rng, settings, self.statistics)
                check_deadline(deadline, lambda: False)
                try:
                    candidate = scope.compile(source)
                except (AeonError, LarkError, ValueError):
                    self.statistics.validation_failed += 1
                    prompt += f"\nThe previous expression failed elaboration: {source}\nTry another expression:\n"
                    continue
                check_deadline(deadline, lambda: False)
                valid = validate(candidate)  # ORIGINAL refinement and shared property/structural gates.
                check_deadline(deadline, lambda: False)
                if not valid:
                    self.statistics.validation_failed += 1
                    ui.register(candidate, None, monotonic() - started, False)
                    prompt += f"\nThe previous expression failed final validation: {source}\nTry another expression:\n"
                    continue
                self.statistics.validation_passed += 1
                try:
                    quality = evaluate(candidate)  # Never score a rejected candidate.
                except InvalidIndividualException:
                    continue
                check_deadline(deadline, lambda: False)
                if not quality:
                    return candidate
                front, improved = update_pareto_front(front, quality, candidate, minimize)
                ui.register(candidate, quality, monotonic() - started, improved)
                if improved:
                    ui.register_front(front, monotonic() - started)
            except DecodingExhausted:
                if front:
                    break
                raise
        if front:
            ui.register_front(front, monotonic() - started)
            return pick_pareto_member(front, seed=self.seed)
        raise SynthesisNotSuccessful("no fully validated type-constrained candidate within the attempt budget")
