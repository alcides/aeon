"""Property-based testing for Aeon (issue #37).

Random inputs for ``@property`` functions are derived automatically from each
argument's type by reusing the synthesis grammar machinery — refinement types
act as preconditions, so generated inputs are valid by construction and no user
generators are required.

- :mod:`aeon.synthesis.pbt.generators` — sample a random ``Term`` of a ``Type``.
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
