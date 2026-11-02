import builtins
from pathlib import Path
from time import sleep

import pytest

from aeon.core.parser import parse_type
from aeon.core.terms import Abstraction, Literal
from aeon.core.types import t_int
from aeon.lsp.server import SYNTHESIZERS
from aeon.synthesis.api import SynthesisNotSuccessful, UnsupportedSynthesisGoal
from aeon.synthesis.decorators import Goal
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.llm import resolve_llm_backend
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer, synthesizer_family, SynthesizerFamily
from aeon.synthesis.modules.type_constrained import TypeConstrainedSynthesizer
from aeon.synthesis.modules.type_constrained.sampling import DecodingExhausted
from aeon.synthesis.modules.type_constrained.transformers_adapter import TransformersAdapter
from aeon.synthesis.modules.type_constrained.types import Scope
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name
from tests.driver import check_and_return_core
from tests.type_constrained_prefix_test import context
from tests.type_constrained_sampling_test import FakeAdapter


class Attempts(FakeAdapter):
    def __init__(self, expressions):
        super().__init__(["<eos>", *expressions], [])
        self.attempt = 0
        self.prompts = []

    def start(self, prompt):
        super().start(prompt)
        self.prompts.append(prompt)
        self.attempt += 1
        self.rankings = [[min(self.attempt, len(self.pieces) - 1)], [0]]


def test_factory_menu_and_seed_do_not_index_ollama(monkeypatch):
    monkeypatch.setenv("AEON_SEED", "73")
    monkeypatch.setenv("AEON_LLM_PROVIDER", "openai")
    backend = make_synthesizer("llm_type_constrained")
    assert isinstance(backend, TypeConstrainedSynthesizer) and backend.seed == 73
    assert "llm_type_constrained" in SYNTHESIZERS
    assert synthesizer_family("llm_type_constrained") is SynthesizerFamily.LLM_ASSISTED
    with pytest.raises(UnsupportedSynthesisGoal, match="token-level"):
        resolve_llm_backend("llm_type_constrained")


def test_full_refinement_gate_precedes_fitness_and_retries(monkeypatch):
    monkeypatch.setenv("AEON_TC_ATTEMPTS", "2")
    adapter = Attempts(["0", "1"])
    backend = TypeConstrainedSynthesizer(adapter_factory=lambda: adapter)
    ctx = context()
    ty = parse_type("{v:Int | v > 0}")
    evaluated = []

    def evaluate(term):
        evaluated.append(term.value)
        return []

    result = backend.synthesize(
        ctx, ty, lambda term: check_type(ctx, term, ty), evaluate, Name("goal", 900), {}, budget=10
    )
    assert isinstance(result, Literal) and result.value == 1
    assert evaluated == [1]
    assert backend.statistics.validation_failed == 1 and backend.statistics.validation_passed == 1
    assert "failed final validation: 0" in adapter.prompts[1]


@pytest.mark.parametrize("minimize,expected", [(True, 1), (False, 3)])
def test_objective_direction_and_pareto_selection(monkeypatch, minimize, expected):
    monkeypatch.setenv("AEON_TC_ATTEMPTS", "3")
    adapter = Attempts(["2", "1", "3"])
    backend = TypeConstrainedSynthesizer(seed=4, adapter_factory=lambda: adapter)
    name = Name("goal", 901)
    result = backend.synthesize(
        context(),
        t_int,
        lambda _: True,
        lambda t: [float(t.value)],
        name,
        {name: {"goals": [Goal(minimize, 1, Name("fitness", 902))]}},
        budget=10,
    )
    assert result.value == expected


def test_no_placeholder_on_repeated_validation_failure(monkeypatch):
    monkeypatch.setenv("AEON_TC_ATTEMPTS", "1")
    adapter = Attempts(["0"])
    backend = TypeConstrainedSynthesizer(adapter_factory=lambda: adapter)
    with pytest.raises(SynthesisNotSuccessful, match="fully validated"):
        backend.synthesize(
            context(), t_int, lambda _: False, lambda _: pytest.fail("fitness ran"), Name("goal", 903), {}
        )


def test_scope_hides_goal_fitness_and_intrinsics():
    name = Name("goal", 904)
    helper = Name("fitness", 905)
    ctx = context().with_var(name, t_int).with_var(helper, t_int)
    scope = Scope(ctx, t_int, name, {name: {"goals": [Goal(True, 1, helper)]}})
    assert not {"goal", "fitness", "native", "native_import", "print"} & scope.bindings.keys()


@pytest.mark.parametrize(
    "source,expression",
    [
        ("def n (x:Int) : {v:Int | v = x + 1} := ?hole;", "x + 1"),
        ("def n : (x:Int) -> {v:Int | v = x + 1} := ?hole;", "fun x => x + 1"),
        ("def n (x:Int) : Bool := ?hole;", "let y := x + 1 in if y > 0 then true else false"),
    ],
)
def test_standard_dispatch_binding_and_full_function_hole(source, expression):
    term, ctx, ectx, metadata = check_and_return_core(source)
    targets = incomplete_functions_and_holes(ctx, term)
    adapter = Attempts([expression])
    backend = TypeConstrainedSynthesizer(adapter_factory=lambda: adapter)
    result = synthesize_holes(ctx, ectx, term, targets, metadata, backend, budget=20)
    candidate = result[targets[0][1][0]]
    assert candidate is not None
    if expression.startswith("fun"):
        assert isinstance(candidate, Abstraction)


@pytest.mark.parametrize(
    "source",
    [
        "def n : Int := ?a; def m : Int := ?b;",
        "def n (1 x:Int) : Int := ?a;",
        "def n : Int := let 1 x := 1 in ?a;",
    ],
)
def test_unsupported_program_scope_fails_before_model(source):
    term, ctx, ectx, metadata = check_and_return_core(source)
    backend = TypeConstrainedSynthesizer(adapter_factory=lambda: pytest.fail("model loaded"))
    with pytest.raises(UnsupportedSynthesisGoal):
        synthesize_holes(ctx, ectx, term, incomplete_functions_and_holes(ctx, term), metadata, backend)


def test_provider_missing_model_and_optional_dependency_errors(monkeypatch):
    backend = TypeConstrainedSynthesizer()
    monkeypatch.setenv("AEON_TC_PROVIDER", "ollama")
    with pytest.raises(UnsupportedSynthesisGoal, match="no token enforcement"):
        backend._adapter()
    monkeypatch.setenv("AEON_TC_PROVIDER", "transformers")
    monkeypatch.delenv("AEON_TC_MODEL", raising=False)
    with pytest.raises(UnsupportedSynthesisGoal, match="AEON_TC_MODEL"):
        backend._adapter()
    original = builtins.__import__

    def absent(name, *args, **kwargs):
        if name == "transformers":
            raise ImportError("absent")
        return original(name, *args, **kwargs)

    monkeypatch.setattr(builtins, "__import__", absent)
    with pytest.raises(UnsupportedSynthesisGoal, match="llm-type-constrained"):
        TransformersAdapter.load("unused")


def test_adapter_rejects_padded_vocabulary_ids_without_changing_model_input():
    class Model:
        def eval(self):
            return self

    class Tokenizer:
        eos_token_id = 0
        all_special_ids = [0]

        def decode(self, ids, **kwargs):
            if 999 in ids:
                raise IndexError("padded model vocabulary")
            return "prompt"

    adapter = TransformersAdapter(Model(), Tokenizer())
    adapter.ids = [1]
    adapter.prompt_text = "prompt"
    assert not adapter.preview(999).stable
    assert adapter.ids == [1]


def test_single_deadline_rejects_late_model_result():
    adapter = Attempts(["0"])
    original = adapter.scores

    def slow():
        sleep(0.02)
        return original()

    adapter.scores = slow
    backend = TypeConstrainedSynthesizer(adapter_factory=lambda: adapter)
    with pytest.raises(DecodingExhausted):
        backend.synthesize(
            context(), t_int, lambda _: pytest.fail("validation ran"), lambda _: [], Name("n", 98), {}, budget=0.01
        )
    assert adapter.commits == []


@pytest.mark.parametrize(
    "filename,expression",
    [
        ("application.ae", "positive x"),
        ("conditional_let.ae", "let y := x + 1 in if y > 0 then y else 0 - y"),
        ("function.ae", "fun x => x + 1"),
        ("refinement_retry.ae", "1"),
    ],
)
def test_documented_source_examples(filename, expression):
    source = (Path(__file__).parents[1] / "examples/synthesis/type_constrained" / filename).read_text()
    term, ctx, ectx, metadata = check_and_return_core(source)
    adapter = Attempts([expression])
    backend = TypeConstrainedSynthesizer(adapter_factory=lambda: adapter)
    targets = incomplete_functions_and_holes(ctx, term)
    result = synthesize_holes(ctx, ectx, term, targets, metadata, backend, budget=20)
    assert result[targets[0][1][0]] is not None
    assert backend.statistics.validation_passed > 0
    if filename == "application.ae":
        assert "answer 0" in adapter.prompts[0]
