"""Property-based testing for Aeon (issue #37).

Inputs for ``@property`` functions are derived automatically from each argument's
type using selectable synthesis backends. Every proposal is typechecked before
use, so refinement types act as preconditions without user-written generators.

- :mod:`aeon.synthesis.pbt.generators` — sample a checked ``Term`` of a ``Type``.
- :mod:`aeon.synthesis.pbt.runner` — discover, generate, check, and report.
"""

from aeon.synthesis.pbt.runner import (
    ExampleResult,
    PropertyCorpus,
    PropertyResult,
    make_property_fitness,
    property_corpora_for_target,
    run_examples,
    run_properties,
)

__all__ = [
    "ExampleResult",
    "PropertyCorpus",
    "PropertyResult",
    "make_property_fitness",
    "property_corpora_for_target",
    "run_examples",
    "run_properties",
]
