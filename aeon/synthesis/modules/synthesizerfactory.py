from enum import Enum

import os

from aeon.synthesis.api import ProgramSynthesizer, Synthesizer
from aeon.synthesis.grammar.ge_synthesis import GESynthesizer
from aeon.synthesis.grammar.genomic_ng import GenomicNGSynthesizer
from aeon.synthesis.modules.float_ng import FloatHoleNGSynthesizer
from aeon.synthesis.modules.ortools_cpsat import CPSatHoleSynthesizer
from aeon.synthesis.modules.lta import LTASynthesizer
from aeon.synthesis.modules.synquid.synthesizer import SynquidSynthesizer
from aeon.synthesis.modules.llm import LLMSynthesizer
from aeon.synthesis.modules.decision_tree import DecisionTreeSynthesizer
from aeon.synthesis.modules.smt_synthesizer import SMTSynthesizer
from aeon.synthesis.modules.sygus import SygusSynthesizer
from aeon.synthesis.modules.tdsyn.synthesizer import TDSynSynthesizer
from aeon.synthesis.modules.symetric import SymetricSynthesizer
from aeon.synthesis.modules.fta import FTASynthesizer
from aeon.synthesis.modules.afta import AFTASynthesizer
from aeon.synthesis.modules.cata import CATASynthesizer
from aeon.synthesis.modules.contata.synthesizer import ContataSynthesizer
from aeon.synthesis.tactics import TacticRandomSynthesizer


class SynthesizerFamily(str, Enum):
    """High-level synthesis backend families shown grouped in the IDE."""

    EXHAUSTIVE = "Exhaustive"
    RANDOM = "Random"
    EVOLUTIONARY = "Evolutionary"
    LLM = "LLM"


# Display order for synthesis families in tooling (info view, menus).
SYNTHESIZER_FAMILY_ORDER: tuple[SynthesizerFamily, ...] = (
    SynthesizerFamily.EXHAUSTIVE,
    SynthesizerFamily.RANDOM,
    SynthesizerFamily.EVOLUTIONARY,
    SynthesizerFamily.LLM,
)


# Human-readable names for the synthesizer backends, shown in tooling such as
# the VS Code "Synthesize" refactor menu. Keys are the internal ``-s`` ids
# accepted by :func:`make_synthesizer`.
SYNTHESIZER_LABELS: dict[str, str] = {
    "gp": "Genetic Programming",
    "enumerative": "Enumerative Search",
    "random_search": "Random Search",
    "1p1": "(1+1) Evolutionary Strategy",
    "hc": "Hill Climbing",
    "synquid": "Synquid (type-directed)",
    "llm": "LLM-based (Ollama)",
    "decision_tree": "Decision Tree (from examples)",
    "smt": "SMT-guided (z3)",
    "sygus": "SyGuS (SMT)",
    "tdsyn": "Type-directed Synthesis",
    "tdsyn_enumerative": "Type-directed Synthesis (enumerative)",
    "tdsyn_random": "Type-directed Synthesis (random)",
    "ng": "Nevergrad grammatical-evolution (NGOpt)",
    "ng_cma": "Nevergrad grammatical-evolution (CMA-ES)",
    "ng_de": "Nevergrad grammatical-evolution (Differential Evolution)",
    "ng_pso": "Nevergrad grammatical-evolution (PSO)",
    "ng_float": "Nevergrad joint Float-hole optimisation (NGOpt)",
    "ng_float_cma": "Nevergrad joint Float-hole optimisation (CMA-ES)",
    "ortools": "OR-Tools CP-SAT (exact/fixed-point numeric-hole optimisation)",
    "tactics": "Tactic Search (Lean-style)",
    "lta": "Liquid Tree Automata",
    "symetric": "Metric Synthesis",
    "fta": "Finite Tree Automata (FTA)",
    "afta": "Abstraction-refinement FTA",
    "cata": "Constraint-annotated Tree Automata",
    "contata": "Constraint-annotated Tree Automata (version space, from examples)",
}


SYNTHESIZER_FAMILIES: dict[str, SynthesizerFamily] = {
    # Exhaustive — complete or constraint-directed search over a finite/decidable space.
    "enumerative": SynthesizerFamily.EXHAUSTIVE,
    "tdsyn": SynthesizerFamily.EXHAUSTIVE,
    "tdsyn_enumerative": SynthesizerFamily.EXHAUSTIVE,
    "synquid": SynthesizerFamily.EXHAUSTIVE,
    "smt": SynthesizerFamily.EXHAUSTIVE,
    "sygus": SynthesizerFamily.EXHAUSTIVE,
    "decision_tree": SynthesizerFamily.EXHAUSTIVE,
    "fta": SynthesizerFamily.EXHAUSTIVE,
    "afta": SynthesizerFamily.EXHAUSTIVE,
    "cata": SynthesizerFamily.EXHAUSTIVE,
    "contata": SynthesizerFamily.EXHAUSTIVE,
    "lta": SynthesizerFamily.EXHAUSTIVE,
    "symetric": SynthesizerFamily.EXHAUSTIVE,
    "xfta": SynthesizerFamily.EXHAUSTIVE,
    "ortools": SynthesizerFamily.EXHAUSTIVE,
    "ortools_int": SynthesizerFamily.EXHAUSTIVE,
    "cpsat": SynthesizerFamily.EXHAUSTIVE,
    # Random — stochastic sampling over the grammar/search space.
    "random_search": SynthesizerFamily.RANDOM,
    "tdsyn_random": SynthesizerFamily.RANDOM,
    "tactics": SynthesizerFamily.RANDOM,
    # Evolutionary — population- or trajectory-based metaheuristic search.
    "gp": SynthesizerFamily.EVOLUTIONARY,
    "hc": SynthesizerFamily.EVOLUTIONARY,
    "1p1": SynthesizerFamily.EVOLUTIONARY,
    "ng": SynthesizerFamily.EVOLUTIONARY,
    "genomic_ng": SynthesizerFamily.EVOLUTIONARY,
    "ng_cma": SynthesizerFamily.EVOLUTIONARY,
    "ng_de": SynthesizerFamily.EVOLUTIONARY,
    "ng_pso": SynthesizerFamily.EVOLUTIONARY,
    "ng_float": SynthesizerFamily.EVOLUTIONARY,
    "float_ng": SynthesizerFamily.EVOLUTIONARY,
    "ng_float_cma": SynthesizerFamily.EVOLUTIONARY,
    # LLM — large-language-model guided synthesis.
    "llm": SynthesizerFamily.LLM,
}


def synthesizer_label(module: str) -> str:
    """A readable display name for synthesizer id ``module`` (falls back to the
    id itself for any backend without an explicit label)."""
    return SYNTHESIZER_LABELS.get(module, module)


def synthesizer_family(module: str) -> SynthesizerFamily:
    """The high-level family of synthesizer id ``module``."""
    return SYNTHESIZER_FAMILIES.get(module, SynthesizerFamily.RANDOM)


def synthesizer_family_label(module: str) -> str:
    """Human-readable family name for synthesizer id ``module``."""
    return synthesizer_family(module).value


def sort_synthesizer_ids(ids: list[str]) -> list[str]:
    """Order synthesizer ids by family (Exhaustive → Random → Evolutionary → LLM)
    then by display label within each family."""
    family_rank = {fam: i for i, fam in enumerate(SYNTHESIZER_FAMILY_ORDER)}

    def key(module: str) -> tuple[int, str]:
        return (family_rank.get(synthesizer_family(module), len(family_rank)), synthesizer_label(module).casefold())

    return sorted(ids, key=key)


def make_synthesizer(module: str) -> Synthesizer | ProgramSynthesizer:
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
        case "llm":
            return LLMSynthesizer()
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
        case "symetric" | "xfta":
            return SymetricSynthesizer()
        case "fta":
            return FTASynthesizer()
        case "afta":
            return AFTASynthesizer()
        case "cata":
            return CATASynthesizer()
        case "contata":
            return ContataSynthesizer()
        case _:
            assert False, f"Not supported synthesizer with name {module}"
