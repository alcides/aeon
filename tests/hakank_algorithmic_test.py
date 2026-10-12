"""Algorithmic goals must compute their answers rather than embed them."""

from scripts.generate_hakank_algorithmic import models
from tests.ortools_cpsat_test import _parse, _solve, _values


def test_euler_one_matches_independent_enumeration():
    model = models()[0]
    source = model.render({"source_url": "https://example.org/euler1"})
    mapping = _values(_solve(_parse(source)))
    assert mapping["h_answer"] == sum(n for n in range(1000) if n % 3 == 0 or n % 5 == 0)
