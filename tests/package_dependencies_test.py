"""Installed AeonLang metadata must agree without uv-only dependency overrides."""

from importlib.metadata import requires, version

from packaging.requirements import Requirement


def test_aeonlang_dependency_metadata_agree():
    for raw in requires("AeonLang") or []:
        requirement = Requirement(raw)
        if requirement.marker and not requirement.marker.evaluate({"extra": ""}):
            continue
        assert version(requirement.name) in requirement.specifier, (
            f"AeonLang requires {requirement}, installed {version(requirement.name)}"
        )


def test_geneticengine_is_not_a_runtime_dependency():
    """GeneticEngine was removed; keep packaging free of it."""
    names = []
    for raw in requires("AeonLang") or []:
        requirement = Requirement(raw)
        if requirement.marker and not requirement.marker.evaluate({"extra": ""}):
            continue
        names.append(requirement.name.lower().replace("_", "-"))
    assert "geneticengine" not in names


def test_dead_and_optional_deps_are_not_required():
    """Heavy / unused packages belong in extras, not the core install."""
    names = []
    for raw in requires("AeonLang") or []:
        requirement = Requirement(raw)
        if requirement.marker and not requirement.marker.evaluate({"extra": ""}):
            continue
        names.append(requirement.name.lower().replace("_", "-"))
    for forbidden in (
        "pathos",
        "zstandard",
        "pandas",
        "ollama",
        "pillow",
        "scikit-learn",
        "scikit-image",
        "psb2",
        "torch",
    ):
        assert forbidden not in names, f"{forbidden} should not be a required dependency"
