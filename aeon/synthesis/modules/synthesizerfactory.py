from aeon.synthesis.api import Synthesizer
from aeon.synthesis.grammar.ge_synthesis import GESynthesizer
from aeon.synthesis.modules.synquid.synthesizer import SynquidSynthesizer


def make_synthesizer(module: str) -> Synthesizer:
    match module:
        case "GE":
            return GESynthesizer()
        case "synquid":
            return SynquidSynthesizer()
        case _:
            assert False, f"Not supported synthesizer with name {module}"