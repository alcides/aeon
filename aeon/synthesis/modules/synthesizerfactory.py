import os

from aeon.synthesis.api import Synthesizer
from aeon.synthesis.grammar.ge_synthesis import GESynthesizer
from aeon.synthesis.modules.lta import LTASynthesizer
from aeon.synthesis.modules.synquid.synthesizer import SynquidSynthesizer
from aeon.synthesis.modules.llm import LLMSynthesizer
from aeon.synthesis.modules.decision_tree import DecisionTreeSynthesizer
from aeon.synthesis.modules.smt_synthesizer import SMTSynthesizer
from aeon.synthesis.modules.tdsyn.synthesizer import TDSynSynthesizer
from aeon.synthesis.tactics import TacticRandomSynthesizer


def make_synthesizer(module: str) -> Synthesizer:
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
        case "synquid":
            return SynquidSynthesizer()
        case "llm":
            return LLMSynthesizer()
        case "decision_tree":
            return DecisionTreeSynthesizer()
        case "smt":
            return SMTSynthesizer()
        case "tdsyn" | "tdsyn_enumerative":
            return TDSynSynthesizer(mode="enumerative", seed=seed)
        case "tdsyn_random":
            return TDSynSynthesizer(mode="random", seed=seed)
        case "tactics":
            return TacticRandomSynthesizer(seed=seed)
        case "lta":
            return LTASynthesizer()
        case _:
            assert False, f"Not supported synthesizer with name {module}"
