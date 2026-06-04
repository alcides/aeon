"""Property-based testing for Aeon (issue #37).

Random inputs for ``@property`` functions are derived automatically from each
argument's type by reusing the synthesis grammar machinery — refinement types
act as preconditions, so generated inputs are valid by construction and no user
generators are required.

- :mod:`aeon.synthesis.pbt.generators` — sample a random ``Term`` of a ``Type``.
- :mod:`aeon.synthesis.pbt.runner` — discover, generate, check, and report.
"""

from aeon.synthesis.pbt.runner import PropertyResult, run_properties

__all__ = ["PropertyResult", "run_properties"]
