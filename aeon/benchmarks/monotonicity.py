"""Synthesize unary Aeon functions subject to universal refinement contracts.

The open task is an *unproved* specification, not an accepted program. The
ordinary compiler verifies each completed candidate against every refinement,
including the relational contract over arbitrary ordered inputs. Python only
orchestrates Aeon's existing synthesizers and compiler; it does not implement
the function, enumerate input pairs, or provide axioms about monotonicity.
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import math
from pathlib import Path
from time import monotonic
from typing import Literal

from lark.exceptions import UnexpectedInput
from z3.z3types import Z3Exception

from aeon.core.terms import Term
from aeon.core.types import RefinedType, top, t_int
from aeon.core.liquid import LiquidLiteralBool
from aeon.errors import LiquidTypeCheckingFailedRelation
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.sugar.lifting import lift
from aeon.sugar.parser import parse_expression
from aeon.sugar.program import SApplication, SIf, SLiteral, STerm, SVar
from aeon.synthesis.api import SynthesisNotSuccessful, Synthesizer
from aeon.synthesis.identification import get_holes_info, incomplete_functions_and_holes
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import ReflectedBinder, UninterpretedBinder, VariableBinder
from aeon.typechecking.liquid import LiquidTypeCheckException
from aeon.typechecking.entailment import entailment_context
from aeon.typechecking.typeinfer import check
from aeon.utils.pprint import pretty_print_sterm
from aeon.verification.smt import model_for_invalid, render_counterexample
from aeon.verification.vcs import Implication, LiquidConstraint

TASKS = ("nondecreasing", "strict", "identity", "shift", "relu")
DEFAULT_TASK_DIR = Path(__file__).resolve().parents[2] / "examples" / "synthesis" / "monotonicity"
_OPS = {"+", "-", "*", "<", "<=", ">", ">=", "==", "!=", "&&", "||", "!"}
_VALUES = (VariableBinder, UninterpretedBinder, ReflectedBinder)


@dataclasses.dataclass(frozen=True)
class Failure:
    obligation: str
    counterexample: str | None


@dataclasses.dataclass(frozen=True)
class ProofResult:
    status: Literal["proved", "disproved", "unproven", "unsupported"]
    candidate: str
    failures: tuple[Failure, ...] = ()
    reason: str | None = None

    @property
    def accepted(self) -> bool:
        return self.status == "proved"


def _integer_constant(term: STerm) -> bool:
    if isinstance(term, SLiteral):
        return type(term.value) is int
    if isinstance(term, SApplication) and isinstance(term.fun, SApplication):
        head = term.fun.fun
        return (
            isinstance(head, SVar)
            and head.name.name in {"+", "-", "*"}
            and _integer_constant(term.fun.arg)
            and _integer_constant(term.arg)
        )
    return False


def _supported(term: STerm) -> bool:
    """Pure, total linear integer arithmetic, Booleans, and conditionals.

    Multiplication needs a constant operand. Exclude division/modulo, Float,
    unknown functions, recursion, holes, FFI, annotations and arbitrary lets.
    The compiler still checks types; this is a semantic-fragment restriction,
    not a parallel implementation of Aeon's type checker.
    """
    if isinstance(term, SLiteral):
        return type(term.value) in (int, bool)
    if isinstance(term, SVar):
        return term.name.name == "x"
    if isinstance(term, SIf):
        return all(_supported(t) for t in (term.cond, term.then, term.otherwise))
    if isinstance(term, SApplication):
        args: list[STerm] = []
        head: STerm = term
        while isinstance(head, SApplication):
            args.insert(0, head.arg)
            head = head.fun
        if not isinstance(head, SVar) or head.name.name not in _OPS:
            return False
        if len(args) != (1 if head.name.name == "!" else 2) or not all(_supported(a) for a in args):
            return False
        return head.name.name != "*" or any(_integer_constant(a) for a in args)
    return False


def _driver() -> AeonDriver:
    return AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 10, no_main=True))


class MonotonicityBenchmark:
    def __init__(self, task: str, task_dir: Path = DEFAULT_TASK_DIR):
        if task not in TASKS:
            raise ValueError(f"Unknown monotonicity task: {task}")
        self.task = task
        self.path = task_dir / f"{task}.ae"
        self.source = self.path.read_text(encoding="utf-8")
        if self.source.count("?body") != 1:
            raise ValueError("A benchmark must have exactly one ?body hole")
        driver = _driver()
        errors = list(driver.parse(filename="<stdin>", aeon_code=self.source))
        # The unresolved f cannot prove its relational refinement. Retain the
        # compiler's partial core ONLY to recover the search scope and goal;
        # never treat this open specification as a verified program.
        if any(not isinstance(e, LiquidTypeCheckingFailedRelation) for e in errors):
            raise ValueError("Benchmark contains non-refinement compilation errors")
        if driver.core is None or driver.typing_ctx is None:
            raise ValueError("Benchmark did not reach core generation")
        targets = incomplete_functions_and_holes(driver.typing_ctx, driver.core)
        if len(targets) != 1 or targets[0][0].name != "f" or len(targets[0][1]) != 1:
            raise ValueError("Only the body of unary f may be synthesized")
        self.function = targets[0][0]
        self.hole = targets[0][1][0]
        holes = get_holes_info(driver.typing_ctx, driver.core, top, targets, refined_types=True)
        self.goal, ctx = holes[self.hole]
        input_types = [ty for name, ty in ctx.vars() if name.name == "x"]
        if len(input_types) != 1 or not isinstance(input_types[0], RefinedType) or input_types[0].type != t_int:
            raise ValueError("Expected one refined Int input x")
        input_type = input_types[0]
        impossible = Implication(
            input_type.name, t_int, input_type.refinement, LiquidConstraint(LiquidLiteralBool(False))
        )
        if model_for_invalid(impossible) is None:
            raise ValueError("Input domain is empty or could not be shown nonempty")
        # No self calls, proof witnesses, natives, or auxiliary functions in
        # the grammar. The hole has only x; x1/x2 belong to the separate proof.
        entries = [e for e in ctx.entries if not isinstance(e, _VALUES) or e.name.name in _OPS | {"x"}]
        self.ctx = dataclasses.replace(ctx, entries=entries)
        self._results: dict[str, ProofResult] = {}

    def completed_source(self, candidate: str) -> str:
        return self.source.replace("?body", f"({candidate})")

    def verify(self, candidate: str) -> ProofResult:
        if candidate in self._results:
            return self._results[candidate]
        try:
            expression = parse_expression(candidate)
        except UnexpectedInput as exc:
            return ProofResult("unsupported", candidate, reason=f"Not an Aeon expression: {exc}")
        if not _supported(expression):
            return ProofResult("unsupported", candidate, reason="Outside the pure linear-Int/Boolean fragment")
        driver = _driver()
        try:
            canonical = pretty_print_sterm(expression, top_level=False)
            errors = list(driver.parse(filename="<stdin>", aeon_code=self.completed_source(canonical)))
        except (Z3Exception, LiquidTypeCheckException, AssertionError) as exc:
            return ProofResult("unproven", candidate, reason=f"Verification could not complete: {exc}")
        failures = tuple(
            Failure(str(error.failed_predicate()), error.counterexample())
            for error in errors
            if isinstance(error, LiquidTypeCheckingFailedRelation)
        )
        if errors and driver.core is not None and driver.typing_ctx is not None:
            # Diagnostic simplification can discard a reflected declaration
            # still needed to reconstruct its model. Query the original VC,
            # not an unconstrained/uninterpreted replacement for f.
            try:
                original_vc = entailment_context(driver.typing_ctx, check(driver.typing_ctx, driver.core, top))
                witness = render_counterexample(original_vc)
            except (Z3Exception, LiquidTypeCheckException, AssertionError, KeyError):
                witness = None
            if witness is not None:
                failures = (
                    Failure("Whole-program refinement obligations (with reflected definitions)", witness),
                    *failures,
                )
        if not errors:
            result = ProofResult("proved", candidate)
        elif any(f.counterexample is not None for f in failures):
            result = ProofResult("disproved", candidate, failures)
        else:
            # A Boolean failure alone does not distinguish sat from unknown.
            # Only an actual solver witness justifies "disproved". Unknown,
            # unsupported translation, or unrenderable witnesses stay unproven.
            result = ProofResult("unproven", candidate, failures, "No proof or concrete counterexample available")
        self._results[candidate] = result
        return result

    def synthesize(self, backend: str = "enumerative", budget: float = 10) -> ProofResult | None:
        if not math.isfinite(budget) or budget <= 0:
            raise ValueError("Budget must be positive and finite")
        synthesizer = make_synthesizer(backend)
        if not isinstance(synthesizer, Synthesizer):
            raise ValueError("Use a per-hole synthesis backend")

        def validate(term: Term) -> bool:
            candidate = pretty_print_sterm(lift(term), top_level=False)
            return self.verify(candidate).accepted

        try:
            term = synthesizer.synthesize(
                ctx=self.ctx,
                type=self.goal,
                validate=validate,
                evaluate=lambda _term: [],
                fun_name=self.function,
                metadata={},
                budget=budget,
                ui=SilentSynthesisUI(),
            )
        except SynthesisNotSuccessful:
            return None
        if term is None:
            return None
        candidate = pretty_print_sterm(lift(term), top_level=False)
        proof = self.verify(candidate)
        # Independently enforce the contract even if a backend ignores validate.
        return proof if proof.accepted else None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--task", choices=TASKS, action="append", help="Default: all five tasks")
    parser.add_argument("--task-dir", type=Path, default=DEFAULT_TASK_DIR)
    parser.add_argument("--backend", default="enumerative")
    parser.add_argument("--budget", type=float, default=10)
    parser.add_argument("--candidate", help="Verify an expression instead of searching")
    args = parser.parse_args()
    success = True
    for task in args.task or TASKS:
        benchmark = MonotonicityBenchmark(task, args.task_dir)
        start = monotonic()
        result = (
            benchmark.verify(args.candidate)
            if args.candidate is not None
            else benchmark.synthesize(args.backend, args.budget)
        )
        report = dataclasses.asdict(result) if result else {"status": "no_solution"}
        print(json.dumps({"task": task, "elapsed": monotonic() - start, **report}))
        success = success and result is not None and result.accepted
    return 0 if success else 2


if __name__ == "__main__":
    raise SystemExit(main())
