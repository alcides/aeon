from enum import Enum

import os

from aeon.synthesis.api import ProgramSynthesizer, Synthesizer, UnknownSynthesizerError
from aeon.synthesis.grammar.ge_synthesis import GESynthesizer
from aeon.synthesis.grammar.genomic_ng import GenomicNGSynthesizer
from aeon.synthesis.modules.float_ng import FloatHoleNGSynthesizer
from aeon.synthesis.modules.ortools_cpsat import CPSatHoleSynthesizer
from aeon.synthesis.modules.lta import LTASynthesizer
from aeon.synthesis.modules.synquid.synthesizer import SynquidSynthesizer
from aeon.synthesis.modules.llm import (
    LLM_OLLAMA_MODELS,
    LLM_OPENAI_SYNTHESIZER_ID,
    LLMSynthesizer,
    is_llm_synthesizer,
    llm_synthesizer_label,
    resolve_llm_backend,
)
from aeon.synthesis.modules.decision_tree import DecisionTreeSynthesizer
from aeon.synthesis.modules.smt_synthesizer import SMTSynthesizer
from aeon.synthesis.modules.sygus import SygusSynthesizer
from aeon.synthesis.modules.tdsyn.synthesizer import TDSynSynthesizer
from aeon.synthesis.modules.rust_enum import RustEnumSynthesizerWrapper
from aeon.synthesis.tactics import TacticRandomSynthesizer


class SynthesizerFamily(str, Enum):
    """High-level synthesis backend families shown grouped in the IDE."""

    TYPE_DIRECTED = "Type-directed"
    EXAMPLE_DRIVEN = "Example-driven"
    CONSTRAINT_SOLVING = "Constraint solving"
    AUTOMATA = "Automata"
    GRAMMAR_SEARCH = "Grammar search"
    METAHEURISTIC = "Metaheuristic"
    LLM_ASSISTED = "LLM-assisted"


# Display order for synthesis families in tooling (info view, menus).
SYNTHESIZER_FAMILY_ORDER: tuple[SynthesizerFamily, ...] = (
    SynthesizerFamily.TYPE_DIRECTED,
    SynthesizerFamily.EXAMPLE_DRIVEN,
    SynthesizerFamily.CONSTRAINT_SOLVING,
    SynthesizerFamily.AUTOMATA,
    SynthesizerFamily.GRAMMAR_SEARCH,
    SynthesizerFamily.METAHEURISTIC,
    SynthesizerFamily.LLM_ASSISTED,
)


# Human-readable names for the synthesizer backends, shown in tooling such as
# the VS Code "Synthesize" refactor menu. Keys are the internal ``-s`` ids
# accepted by :func:`make_synthesizer`.
SYNTHESIZER_LABELS: dict[str, str] = {
    "tdsyn": "Type-directed synthesis (BFS)",
    "tdsyn_enumerative": "Type-directed synthesis (BFS)",
    "tdsyn_random": "Type-directed synthesis (Random Walk)",
    "synquid": "Synquid enumeration (Q-guided)",
    "tactics": "Tactic search (random)",
    "decision_tree": "Decision tree regression (from examples)",
    "contata": "Version-space synthesis (from I/O examples)",
    "smt": "SMT model finding (Z3)",
    "sygus": "SyGuS translation (CVC5)",
    "ortools": "CP-SAT optimisation (OR-Tools)",
    "ortools_int": "CP-SAT optimisation (OR-Tools)",
    "cpsat": "CP-SAT optimisation (OR-Tools)",
    "fta": "Finite tree automata (library compose)",
    "afta": "Abstraction-refinement FTA (from examples)",
    "cata": "Constraint tree automata (relational)",
    "lta": "Liquid tree automata (refined compose)",
    "symetric": "Metric-guided composition (diversity)",
    "xfta": "Metric-guided composition (diversity)",
    "enumerative": "Grammar enumeration (enumerative)",
    "random_search": "Grammar enumeration (random)",
    "gp": "Genetic programming (default)",
    "hc": "Hill climbing",
    "1p1": "(1+1) evolution strategy",
    "ng": "Nevergrad · grammar (NGOpt)",
    "genomic_ng": "Nevergrad · grammar (NGOpt)",
    "ng_cma": "Nevergrad · grammar (CMA-ES)",
    "ng_de": "Nevergrad · grammar (differential evolution)",
    "ng_pso": "Nevergrad · grammar (PSO)",
    "ng_float": "Nevergrad · float holes (NGOpt)",
    "float_ng": "Nevergrad · float holes (NGOpt)",
    "ng_float_cma": "Nevergrad · float holes (CMA-ES)",
    **{sid: llm_synthesizer_label(sid) for sid in LLM_OLLAMA_MODELS},
    LLM_OPENAI_SYNTHESIZER_ID: llm_synthesizer_label(LLM_OPENAI_SYNTHESIZER_ID),
}


SYNTHESIZER_FAMILIES: dict[str, SynthesizerFamily] = {
    # Type-directed — decompose the goal type and fill holes structurally.
    "tdsyn": SynthesizerFamily.TYPE_DIRECTED,
    "tdsyn_enumerative": SynthesizerFamily.TYPE_DIRECTED,
    "tdsyn_random": SynthesizerFamily.TYPE_DIRECTED,
    "synquid": SynthesizerFamily.TYPE_DIRECTED,
    "tactics": SynthesizerFamily.TYPE_DIRECTED,
    # Example-driven — learn from @example / @csv_data I/O.
    "decision_tree": SynthesizerFamily.EXAMPLE_DRIVEN,
    "contata": SynthesizerFamily.EXAMPLE_DRIVEN,
    # Constraint solving — SMT / CP-SAT exact solvers.
    "smt": SynthesizerFamily.CONSTRAINT_SOLVING,
    "sygus": SynthesizerFamily.CONSTRAINT_SOLVING,
    "ortools": SynthesizerFamily.CONSTRAINT_SOLVING,
    "ortools_int": SynthesizerFamily.CONSTRAINT_SOLVING,
    "cpsat": SynthesizerFamily.CONSTRAINT_SOLVING,
    # Automata — compose library functions via tree automata.
    "fta": SynthesizerFamily.AUTOMATA,
    "afta": SynthesizerFamily.AUTOMATA,
    "cata": SynthesizerFamily.AUTOMATA,
    "lta": SynthesizerFamily.AUTOMATA,
    "symetric": SynthesizerFamily.AUTOMATA,
    "xfta": SynthesizerFamily.AUTOMATA,
    # Grammar search — sample or enumerate syntax trees from a grammar.
    "enumerative": SynthesizerFamily.GRAMMAR_SEARCH,
    "random_search": SynthesizerFamily.GRAMMAR_SEARCH,
    # Metaheuristic — improve candidates with a fitness landscape.
    "gp": SynthesizerFamily.METAHEURISTIC,
    "hc": SynthesizerFamily.METAHEURISTIC,
    "1p1": SynthesizerFamily.METAHEURISTIC,
    "ng": SynthesizerFamily.METAHEURISTIC,
    "genomic_ng": SynthesizerFamily.METAHEURISTIC,
    "ng_cma": SynthesizerFamily.METAHEURISTIC,
    "ng_de": SynthesizerFamily.METAHEURISTIC,
    "ng_pso": SynthesizerFamily.METAHEURISTIC,
    "ng_float": SynthesizerFamily.METAHEURISTIC,
    "float_ng": SynthesizerFamily.METAHEURISTIC,
    "ng_float_cma": SynthesizerFamily.METAHEURISTIC,
    # LLM-assisted — generate candidates from natural language.
    **dict.fromkeys(LLM_OLLAMA_MODELS, SynthesizerFamily.LLM_ASSISTED),
    LLM_OPENAI_SYNTHESIZER_ID: SynthesizerFamily.LLM_ASSISTED,
}

_BUILTIN_SYNTHESIZER_IDS = frozenset(
    {
        "random_search",
        "enumerative",
        "gp",
        "1p1",
        "hc",
        "genomic_ng",
        "ng",
        "ng_cma",
        "ng_de",
        "ng_pso",
        "ng_float",
        "float_ng",
        "ng_float_cma",
        "ortools",
        "ortools_int",
        "cpsat",
        "synquid",
        "decision_tree",
        "smt",
        "sygus",
        "tdsyn",
        "tdsyn_enumerative",
        "tdsyn_random",
        "tactics",
        "lta",
        "symetric",
        "xfta",
        "fta",
        "afta",
        "cata",
        "contata",
    }
)


def is_known_synthesizer(module: str) -> bool:
    """Whether ``module`` is a valid ``-s``/``--synthesizer`` backend id."""
    return module in _BUILTIN_SYNTHESIZER_IDS or is_llm_synthesizer(module)


def validate_synthesizer(module: str) -> None:
    """Raise :class:`UnknownSynthesizerError` when ``module`` is not a known backend."""
    if not is_known_synthesizer(module):
        raise UnknownSynthesizerError(module)


def synthesizer_label(module: str) -> str:
    """A readable display name for synthesizer id ``module`` (falls back to the
    id itself for any backend without an explicit label)."""
    return SYNTHESIZER_LABELS.get(module, module)


def synthesizer_family(module: str) -> SynthesizerFamily:
    """The high-level family of synthesizer id ``module``."""
    return SYNTHESIZER_FAMILIES.get(module, SynthesizerFamily.GRAMMAR_SEARCH)


def synthesizer_family_label(module: str) -> str:
    """Human-readable family name for synthesizer id ``module``."""
    return synthesizer_family(module).value


def sort_synthesizer_ids(ids: list[str]) -> list[str]:
    """Order synthesizer ids by family then by display label within each family."""
    family_rank = {fam: i for i, fam in enumerate(SYNTHESIZER_FAMILY_ORDER)}

    def key(module: str) -> tuple[int, str]:
        return (family_rank.get(synthesizer_family(module), len(family_rank)), synthesizer_label(module).casefold())

    return sorted(ids, key=key)


def make_synthesizer(module: str) -> Synthesizer | ProgramSynthesizer:
    validate_synthesizer(module)
    # The random seed for stochastic backends is taken from the AEON_SEED
    # environment variable (default 0), so experiments can vary it across runs
    # (e.g. multi-seed benchmarks) without a dedicated CLI flag.
    seed = int(os.environ.get("AEON_SEED", "0"))
    match module:
        case "random_search":
            return GESynthesizer(seed=seed, method="random_search")
        case "enumerative":
            return GESynthesizer(seed=seed, method="enumerative")
        case "gp":
            return GESynthesizer(seed=seed, method="genetic_programming")
        case "1p1":
            return GESynthesizer(seed=seed, method="one_plus_one")
        case "hc":
            return GESynthesizer(seed=seed, method="hill_climbing")
        case "genomic_ng" | "ng":
            return GenomicNGSynthesizer(optimizer="NGOpt", seed=seed)
        case "ng_cma":
            return GenomicNGSynthesizer(optimizer="CMA", seed=seed)
        case "ng_de":
            return GenomicNGSynthesizer(optimizer="DE", seed=seed)
        case "ng_pso":
            return GenomicNGSynthesizer(optimizer="PSO", seed=seed)
        case "ng_float" | "float_ng":
            return FloatHoleNGSynthesizer(optimizer="NGOpt", seed=seed)
        case "ng_float_cma":
            return FloatHoleNGSynthesizer(optimizer="CMA", seed=seed)
        case "ortools" | "ortools_int" | "cpsat":
            return CPSatHoleSynthesizer(seed=seed)
        case "synquid":
            return SynquidSynthesizer()
        case id if id in LLM_OLLAMA_MODELS or id == LLM_OPENAI_SYNTHESIZER_ID:
            model, provider = resolve_llm_backend(id)
            return LLMSynthesizer(model=model, provider=provider)
        case "decision_tree":
            return DecisionTreeSynthesizer()
        case "smt":
            return SMTSynthesizer()
        case "sygus":
            return SygusSynthesizer()
        case "tdsyn" | "tdsyn_enumerative":
            return TDSynSynthesizer(mode="enumerative", seed=seed)
        case "tdsyn_random":
            return TDSynSynthesizer(mode="random", seed=seed)
        case "tactics":
            return TacticRandomSynthesizer(seed=seed)
        case "lta":
            return LTASynthesizer()
        case "rust_enum":
            return RustEnumSynthesizerWrapper()
        case _:
            raise UnknownSynthesizerError(module)
