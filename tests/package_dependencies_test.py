"""Installed metadata must agree without uv-only dependency overrides."""

from importlib.metadata import requires, version

from packaging.requirements import Requirement


def test_geneticengine_and_aeon_dependency_metadata_agree():
    for package in ("AeonLang", "GeneticEngine"):
        for raw in requires(package) or []:
            requirement = Requirement(raw)
            if requirement.marker and not requirement.marker.evaluate({"extra": ""}):
                continue
            assert version(requirement.name) in requirement.specifier, (
                f"{package} requires {requirement}, installed {version(requirement.name)}"
            )
