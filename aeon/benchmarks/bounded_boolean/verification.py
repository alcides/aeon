"""Recheck saved programs as well as portable certificates against pinned tasks."""

from pathlib import Path

from aeon.benchmarks.bounded_boolean.checker import CheckFailure, check, check_import, check_runtime, extract
from aeon.benchmarks.bounded_boolean.corpus import ROOT, case_hashes, case_source, digest, load_case, verify_manifest


def verify_saved(saved: dict, directory: Path, root: Path = ROOT, *, certificate_only: bool = False) -> dict:
    from aeon.benchmarks.bounded_boolean.runner import candidate_digest

    config = saved["config"]
    if config.get("suite", "published") == "local":
        from aeon.benchmarks.bounded_boolean.local import manifest

        inventory = manifest(root)
    else:
        inventory = verify_manifest(root)
    cases = {c["id"]: c for c in inventory["cases"]}
    if config["task"] not in cases:
        raise CheckFailure("translation_failure", "unknown saved task")
    case = cases[config["task"]]
    source = case_source(case, config["bound"], root)
    expected = {"source_sha256": digest(source.encode()), **case_hashes(case, root)}
    if any(config.get(key) != value for key, value in expected.items()):
        raise CheckFailure("translation_failure", "saved result belongs to different source bytes or configuration")
    if "outputs" not in saved:
        raise CheckFailure("no_candidate", "bounded UNSAT or search failure is not a solution certificate")
    if saved.get("candidate_sha256") != candidate_digest(saved["outputs"]):
        raise CheckFailure("structural_failure", "candidate certificate hash mismatch")
    circuit = load_case(case, root)
    result = check(circuit, saved["outputs"], config["bound"])
    result["verification_scope"] = "certificate_only"
    if certificate_only:
        return result
    # Archived v1 coverage embeds portable certificates without candidate files.
    # Label that narrower check explicitly. A named file must never be ignored.
    if "candidate_file" not in saved:
        if config.get("schema_version", 1) >= 2:
            raise CheckFailure("structural_failure", "saved program is missing; use an explicitly archived certificate")
        return result
    filename = saved["candidate_file"]
    if not isinstance(filename, str) or Path(filename).name != filename:
        raise CheckFailure("structural_failure", "candidate must be an adjacent .ae file")
    path = directory / filename
    if not path.is_file():
        raise CheckFailure("structural_failure", "saved candidate file is missing")
    data = path.read_bytes()
    if "candidate_file_sha256" in saved and digest(data) != saved["candidate_file_sha256"]:
        raise CheckFailure("structural_failure", "candidate program hash mismatch")
    from aeon.core.types import top
    from aeon.facade.driver import AeonConfig, AeonDriver
    from aeon.synthesis.identification import term_has_holes
    from aeon.synthesis.uis.api import SilentSynthesisUI
    from aeon.typechecking.typeinfer import check_type

    driver = AeonDriver(AeonConfig("boolean_bounded", SilentSynthesisUI(), 0, no_main=True))
    errors = list(driver.parse(filename=str(path), aeon_code=data.decode()))
    if errors:
        raise CheckFailure("translation_failure", "; ".join(map(str, errors)))
    with driver.session.activate():
        if term_has_holes(driver.core) or not check_type(driver.typing_ctx, driver.core, top):
            raise CheckFailure("type_failure", "saved candidate failed Aeon validation")
        outputs = extract(driver.core, circuit, config["bound"])
        if outputs != saved["outputs"]:
            raise CheckFailure("validation_error", "saved program disagrees with its CNF certificate")
        if check_import(driver.core, circuit) != "equivalent":
            raise CheckFailure("translation_failure", "saved relation disagrees with original task")
        result.update(check_runtime(driver.core, circuit, outputs, driver.evaluation_ctx))
    result["verification_scope"] = "program_and_certificate"
    return result
