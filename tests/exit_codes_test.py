"""The CLI must exit non-zero whenever it reports an error, with a distinct
exit code per error category (see ``aeon.facade.exit_codes``).

Regression context: ``main()`` used to print the errors returned by
``driver.parse`` and fall through to an implicit ``exit 0``, so CI treated
broken programs as passing.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

from aeon.facade.api import (
    CoreSubtypingError,
    ImportError as AeonImportError,
    InstanceResolutionError,
    LinearUnusedError,
    MethodResolutionError,
    NonOrderableComparisonError,
    UnificationFailedError,
    UnificationKindError,
    UnificationSubtypingError,
    UnificationUnknownTypeError,
)
from aeon.facade.exit_codes import ExitCode, error_exit_code

REPO_ROOT = Path(__file__).resolve().parent.parent


# --- Unit: error class -> exit code mapping ---------------------------------


def _make(cls):
    """Errors are dataclasses; field contents are irrelevant to the mapping."""
    return cls.__new__(cls)


@pytest.mark.parametrize(
    "cls,expected",
    [
        (AeonImportError, ExitCode.IMPORT_ERROR),
        (UnificationSubtypingError, ExitCode.TYPE_MISMATCH),
        (UnificationFailedError, ExitCode.UNIFICATION_ERROR),
        (UnificationKindError, ExitCode.KIND_MISMATCH),
        (UnificationUnknownTypeError, ExitCode.UNKNOWN_NAME),
        (MethodResolutionError, ExitCode.METHOD_RESOLUTION_ERROR),
        (InstanceResolutionError, ExitCode.MISSING_INSTANCE),
        (NonOrderableComparisonError, ExitCode.NON_ORDERABLE_COMPARISON),
        # LinearityError specialises CoreTypeCheckingError and must win.
        (LinearUnusedError, ExitCode.LINEARITY_ERROR),
        (CoreSubtypingError, ExitCode.CORE_TYPE_ERROR),
    ],
)
def test_error_exit_code_mapping(cls, expected):
    assert error_exit_code(_make(cls)) == expected


# --- End to end: the CLI process exit status ---------------------------------


def run_aeon(tmp_path: Path, source: str) -> subprocess.CompletedProcess:
    f = tmp_path / "prog.ae"
    f.write_text(source)
    return subprocess.run(
        [sys.executable, "-m", "aeon", "--no-main", "--budget", "1", str(f)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=240,
    )


def test_cli_success_exits_zero(tmp_path):
    r = run_aeon(tmp_path, "def main (x:Int) : Unit := print 42;\n")
    assert r.returncode == ExitCode.SUCCESS, r.stderr


def test_cli_syntax_error(tmp_path):
    r = run_aeon(tmp_path, "def main (x:Int) : Unit := print (1 +;\n")
    assert r.returncode == ExitCode.SYNTAX_ERROR
    assert "Syntax error" in r.stdout


def test_cli_import_error(tmp_path):
    r = run_aeon(tmp_path, "import NoSuchModule;\ndef main (x:Int) : Unit := print 1;\n")
    assert r.returncode == ExitCode.IMPORT_ERROR


def test_cli_type_mismatch(tmp_path):
    r = run_aeon(tmp_path, 'def main (x:Int) : Unit := y : Int := "hello";\n    print y;\n')
    assert r.returncode == ExitCode.TYPE_MISMATCH
    # The error report must still be printed.
    assert "Type mismatch" in r.stdout


def test_cli_unknown_variable(tmp_path):
    r = run_aeon(tmp_path, "def main (x:Int) : Unit := print missing_var;\n")
    assert r.returncode == ExitCode.UNKNOWN_NAME


def test_cli_unknown_qualified_name(tmp_path):
    r = run_aeon(tmp_path, 'import String;\ndef main (x:Int) : Unit := print (String.nope "a");\n')
    assert r.returncode == ExitCode.UNKNOWN_NAME


def test_cli_method_resolution_error(tmp_path):
    r = run_aeon(tmp_path, "def main (x:Int) : Unit := print (1.nonexistent);\n")
    assert r.returncode == ExitCode.METHOD_RESOLUTION_ERROR


def test_cli_invalid_refinement(tmp_path):
    src = (
        'import String;\ndef f (s : {x:String | x.len > 0}) : String := s;\ndef main (x:Int) : Unit := print (f "a");\n'
    )
    r = run_aeon(tmp_path, src)
    assert r.returncode == ExitCode.INVALID_REFINEMENT
