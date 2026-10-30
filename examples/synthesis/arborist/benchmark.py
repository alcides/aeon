"""Reproduce the small lifted-interpretation compression comparison."""

from pathlib import Path

from loguru import logger

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.modules.arborist import ArboristSynthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI


def main() -> None:
    logger.remove()
    print("example,compressed,transitions,merges,contexts,interpreter_steps,validated")
    for name in ("local", "fold"):
        for compress in (True, False):
            driver = AeonDriver(AeonConfig("arborist", SilentSynthesisUI(), 10, no_main=True))
            errors = list(driver.parse(aeon_code=Path(__file__).with_name(f"{name}.ae").read_text()))
            if errors:
                raise RuntimeError(errors)
            driver.has_synth()
            backend = ArboristSynthesizer(compress=compress)
            with driver.session.activate():
                synthesize_holes(
                    driver.typing_ctx,
                    driver.evaluation_ctx,
                    driver.core,
                    driver.incomplete_functions,
                    driver.metadata,
                    backend,
                    10,
                    SilentSynthesisUI(),
                )
            s = backend.stats
            print(
                f"{name},{compress},{s.transitions},{s.merges},{len(backend.reachable)},{s.interpreter_steps},{s.validated}"
            )


if __name__ == "__main__":
    main()
