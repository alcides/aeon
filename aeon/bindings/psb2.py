"""Stable PSB2 fixtures which hand each fitness evaluation its own data."""

from copy import deepcopy
import random
from typing import Any, Callable


def training_data(name: str, n_train: int, n_test: int) -> Callable[[Any], Any]:
    """Sample once, lazily, and copy the same cases for every candidate.

    Candidates may consume or mutate array inputs. Neither that mutation nor
    another call to PSB2's random sampler may change the next evaluation's
    training cases. The private template is never returned to Aeon.
    """
    template = None

    def fresh(_unit: Any) -> Any:
        nonlocal template
        if template is None:
            from psb2 import fetch_examples

            # A fixture copied to a fitness worker before first use must draw
            # the same cases there too. PSB2 seeds the process-wide RNG, so
            # restore it rather than perturbing synthesis search randomness.
            state = random.getstate()
            try:
                template = fetch_examples("path/to/PSB2/datasets/", name, n_train, n_test, format="lists", seed=0)[0]
            finally:
                random.setstate(state)
        return deepcopy(template)

    return fresh
