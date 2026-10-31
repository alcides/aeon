"""Optional real neural inference; no network access or pretrained downloads."""

import pytest

from aeon.synthesis.modules.type_constrained.smoke import run_smoke


def test_real_torch_adapter_masking():
    pytest.importorskip("torch")
    report = run_smoke()
    assert len(report["cases"]) == 3
    assert all(case["validated"] and case["rejected_tokens"] > 0 for case in report["cases"])


def test_real_transformers_adapter_load_and_masking():
    pytest.importorskip("torch")
    pytest.importorskip("transformers")
    report = run_smoke(transformers=True)
    assert len(report["cases"]) == 3
    assert all(case["validated"] and case["tokens"] == 2 for case in report["cases"])
