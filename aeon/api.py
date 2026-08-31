"""Small public Python API for Aeon.

Implementation modules remain private compatibility internals during the
Rust migration. New callers should use this façade for parsing, checking, and
synthesis.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI, SynthesisFormat, SynthesisUI


@dataclass
class Program:
    _driver: AeonDriver
    errors: list[Any]

    def check(self) -> list[Any]:
        return list(self.errors)

    def synthesize(self, backend: str = "gp", budget: int = 60, ui: SynthesisUI | None = None) -> "Program":
        if not self.errors and self._driver.has_synth():
            self._driver.cfg.synthesizer = backend
            self._driver.cfg.synthesis_budget = budget
            self._driver._run_synthesis(ui or SilentSynthesisUI())
        return self

    def run(self) -> Any:
        if self.errors:
            raise ValueError("cannot execute a program with checking errors")
        return self._driver.run()

    def export(self, function: str) -> str:
        if self.errors:
            raise ValueError("cannot export a program with checking errors")
        return self._driver.export(function)


def parse(
    source: str | Path,
    *,
    filename: str | Path | None = None,
    no_main: bool = False,
    strict_decidable: bool = False,
    contracts: bool = False,
) -> Program:
    """Parse, elaborate, and type-check source text or an ``.ae`` file."""
    if isinstance(source, Path):
        filename = filename or source
        source = source.read_text(encoding="utf-8")
    driver = AeonDriver(
        AeonConfig(
            synthesizer="gp",
            synthesis_ui=SilentSynthesisUI(),
            synthesis_budget=60,
            no_main=no_main,
            synthesis_format=SynthesisFormat.DEFAULT,
            strict_decidable=strict_decidable,
            contracts=contracts,
        )
    )
    errors = list(driver.parse(aeon_code=source, filename=str(filename) if filename else None))
    return Program(driver, errors)


def check(source: str | Path, **options: Any) -> list[Any]:
    return parse(source, **options).check()


def synthesize(source: str | Path, *, backend: str = "gp", budget: int = 60, **options: Any) -> Program:
    return parse(source, **options).synthesize(backend=backend, budget=budget)


__all__ = ["Program", "check", "parse", "synthesize"]
