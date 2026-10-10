"""Check installed wheel resources and execution without checkout/PYTHONPATH access."""

import subprocess
import sys
import tempfile

SMOKE = """
from importlib.metadata import version
from pathlib import Path
import aeon
from loguru import logger
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI

logger.remove()

package = Path(aeon.__file__).resolve().parent
assert "site-packages" in str(package), package
assert (package / "sugar" / "aeon_sugar.lark").is_file()
assert (package / "core" / "aeon_core.lark").is_file()
assert (package / "libraries" / "Math.ae").is_file()
driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 0, no_main=True))
errors = list(driver.parse(aeon_code="import Math; def main (u:Int) : Int := Math.abs (-7);", filename="<stdin>"))
assert not errors, errors
assert driver.run() == 7
print("Installed AeonLang", version("AeonLang"), "wheel smoke test passed")
"""


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="aeon-wheel-smoke-") as directory:
        subprocess.run([sys.executable, "-I", "-c", SMOKE], cwd=directory, check=True)


if __name__ == "__main__":
    main()
