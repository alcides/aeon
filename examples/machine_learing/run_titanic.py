# Script to run the Titanic example program and print the accuracy of the decision tree model.

from __future__ import annotations

import math
import os
import sys
from pathlib import Path


REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
AEON_PROGRAM = REPOSITORY_ROOT / "examples" / "machine_learing" / "titanic_dataset.ae"

# Make both ``import aeon`` and the relative CSV path work even when this
# script is launched from another directory.
sys.path.insert(0, str(REPOSITORY_ROOT))
os.chdir(REPOSITORY_ROOT)

from aeon.facade.driver import AeonConfig, AeonDriver  # noqa: E402
from aeon.logger.logger import setup_logger  # noqa: E402
from aeon.synthesis.uis.api import SilentSynthesisUI  # noqa: E402


def run_titanic() -> float:
    # Remove loguru's default DEBUG/INFO sink so this runner prints only the
    # result or a useful error.
    setup_logger()
    config = AeonConfig(
        synthesizer="none",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=0,
        no_main=False,
        contracts=False,
    )
    driver = AeonDriver(config)
    errors = list(driver.parse(str(AEON_PROGRAM)))
    if errors:
        details = "\n".join(f"- {error}" for error in errors)
        raise RuntimeError(f"O programa Aeon não passou a verificação:\n{details}")

    result = driver.run()
    if not isinstance(result, (int, float)):
        raise TypeError(f"Esperava um resultado numérico, mas recebi {type(result).__name__}: {result!r}")
    score = float(result)
    if not math.isfinite(score) or not 0.0 <= score <= 1.0:
        raise ValueError(f"A accuracy devolvida não é válida: {score!r}")
    return score


def main() -> int:
    score = run_titanic()
    print(f"Accuracy da decision tree no Titanic: {score:.4f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
