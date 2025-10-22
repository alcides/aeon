from aeon.synthesis.api import Synthesizer
from aeon.synthesis.grammar.ge_synthesis import GESynthesizer
from aeon.synthesis.modules.synquid.synthesizer import SynquidSynthesizer
from aeon.synthesis.modules.llm import LLMSynthesizer


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
        case _:
            assert False, f"Not supported synthesizer with name {module}"
