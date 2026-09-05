"""The AEON_SEED environment variable seeds the stochastic synthesizers.

`make_synthesizer` reads AEON_SEED (default 0) so multi-seed experiments can
vary the random seed of the stochastic backends without a dedicated CLI flag.
"""

from __future__ import annotations

import pytest

from aeon.synthesis.modules.synthesizerfactory import make_synthesizer

SEEDED_BACKENDS = [
    "random_search",
    "enumerative",
    "gp",
    "1p1",
    "hc",
    "tdsyn",
    "tdsyn_enumerative",
    "tdsyn_random",
    "tactics",
]


@pytest.mark.parametrize("backend", SEEDED_BACKENDS)
def test_aeon_seed_is_threaded(monkeypatch, backend):
    monkeypatch.setenv("AEON_SEED", "123")
    assert make_synthesizer(backend).seed == 123


@pytest.mark.parametrize("backend", SEEDED_BACKENDS)
def test_seed_defaults_to_zero(monkeypatch, backend):
    monkeypatch.delenv("AEON_SEED", raising=False)
    assert make_synthesizer(backend).seed == 0
