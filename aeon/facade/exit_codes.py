"""Process exit codes for the ``aeon`` command-line interface.

Every error category the compiler reports maps to a distinct, stable exit
code, so scripts and CI can react to *what* failed without scraping stdout.

The contract:

* ``0``  — success.
* ``1``  — failing ``--test`` properties/examples, or an internal crash
  (Python's default for an unhandled exception).
* ``2``  — synthesis finished without finding a solution (pre-existing
  contract, relied on by ``run_examples.sh``).
* ``3+`` — compile-time errors, one code per category (see ``ExitCode``).

When a run reports several errors, the process exits with the code of the
*first* error reported.
"""

from __future__ import annotations

from enum import IntEnum

from aeon.facade.api import (
    AeonError,
    CoreTypeCheckingError,
    InstanceResolutionError,
    LinearityError,
    MethodResolutionError,
    ModuleNotFoundAeonError as AeonImportError,
    NonOrderableComparisonError,
    RefinementExecutionHoleError,
    UndecidableRefinementError,
    UnificationFailedError,
    UnificationKindError,
    UnificationSubtypingError,
    UnificationUnknownTypeError,
)


class ExitCode(IntEnum):
    SUCCESS = 0
    TESTS_FAILED_OR_CRASH = 1
    SYNTHESIS_NOT_SUCCESSFUL = 2
    SYNTAX_ERROR = 3
    IMPORT_ERROR = 4
    TYPE_MISMATCH = 5
    UNIFICATION_ERROR = 6
    KIND_MISMATCH = 7
    UNKNOWN_NAME = 8
    METHOD_RESOLUTION_ERROR = 9
    MISSING_INSTANCE = 10
    NON_ORDERABLE_COMPARISON = 11
    LINEARITY_ERROR = 12
    CORE_TYPE_ERROR = 13
    INVALID_REFINEMENT = 14
    UNDECIDABLE_REFINEMENT = 15
    OTHER_ERROR = 16


def error_exit_code(err: AeonError) -> ExitCode:
    """Map an error to its exit code.

    Subclass order matters: ``LinearityError`` specialises
    ``CoreTypeCheckingError``, so it is matched first (mirroring
    ``_error_kind_and_hint`` in ``aeon.__main__``).
    """
    match err:
        case AeonImportError():
            return ExitCode.IMPORT_ERROR
        case UnificationSubtypingError():
            return ExitCode.TYPE_MISMATCH
        case UnificationFailedError():
            return ExitCode.UNIFICATION_ERROR
        case UnificationKindError():
            return ExitCode.KIND_MISMATCH
        case UnificationUnknownTypeError():
            return ExitCode.UNKNOWN_NAME
        case MethodResolutionError():
            return ExitCode.METHOD_RESOLUTION_ERROR
        case InstanceResolutionError():
            return ExitCode.MISSING_INSTANCE
        case NonOrderableComparisonError():
            return ExitCode.NON_ORDERABLE_COMPARISON
        case UndecidableRefinementError():
            return ExitCode.UNDECIDABLE_REFINEMENT
        case RefinementExecutionHoleError():
            return ExitCode.INVALID_REFINEMENT
        case LinearityError():
            return ExitCode.LINEARITY_ERROR
        case CoreTypeCheckingError():
            return ExitCode.CORE_TYPE_ERROR
        case _:
            return ExitCode.OTHER_ERROR
