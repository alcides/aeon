from aeon.synthesis.api import Synthesizer
from aeon.synthesis.grammar.ge_synthesis import GESynthesizer
from aeon.synthesis.modules.synquid.synthesizer import SynquidSynthesizer
from aeon.synthesis.modules.llm import LLMSynthesizer
from aeon.synthesis.modules.decision_tree import DecisionTreeSynthesizer
from aeon.synthesis.modules.smt_synthesizer import SMTSynthesizer
from aeon.synthesis.modules.tdsyn.synthesizer import TDSynSynthesizer
from aeon.synthesis.tactics import TacticRandomSynthesizer


def make_synthesizer(module: str) -> Synthesizer:
    match module:
        case "random_search":
            return GESynthesizer(method="random_search")
        case "enumerative":
            return GESynthesizer(method="enumerative")
        case "gp":
            return GESynthesizer(method="genetic_programming")
        case "1p1":
            return GESynthesizer(method="one_plus_one")
        case "hc":
            return GESynthesizer(method="hill_climbing")
        case "synquid":
            return SynquidSynthesizer()
        case "llm":
            return LLMSynthesizer()
        case "decision_tree":
            return DecisionTreeSynthesizer()
        case "smt":
            return SMTSynthesizer()
        case "tdsyn" | "tdsyn_enumerative":
            return TDSynSynthesizer(mode="enumerative")
        case "tdsyn_random":
            return TDSynSynthesizer(mode="random")
        case "tactics":
            return TacticRandomSynthesizer()
        case _:
            assert False, f"Not supported synthesizer with name {module}"
