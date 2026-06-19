import os

from aeon.synthesis.api import ProgramSynthesizer, Synthesizer
from aeon.synthesis.grammar.ge_synthesis import GESynthesizer
from aeon.synthesis.grammar.genomic_ng import GenomicNGSynthesizer
from aeon.synthesis.modules.float_ng import FloatHoleNGSynthesizer
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
from aeon.synthesis.tactics import TacticRandomSynthesizer


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
    "tactics": "Tactic Search (Lean-style)",
    "lta": "Liquid Tree Automata",
    "symetric": "Metric Synthesis",
    "fta": "Finite Tree Automata (FTA)",
    "afta": "Abstraction-refinement FTA",
    "cata": "Constraint-annotated Tree Automata",
}


def synthesizer_label(module: str) -> str:
    """A readable display name for synthesizer id ``module`` (falls back to the
    id itself for any backend without an explicit label)."""
    return SYNTHESIZER_LABELS.get(module, module)


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
        case _:
            assert False, f"Not supported synthesizer with name {module}"
