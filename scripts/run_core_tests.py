"""Fast mandatory cross-version gate; the single full-suite job remains exhaustive."""

import sys

import pytest

CORE_TESTS = [
    "tests/core_properties_test.py",
    "tests/compilation_session_test.py",
    "tests/compilation_unit_test.py",
    "tests/backend_test.py",
    "tests/substitutions_test.py",
    "tests/type_substitution_capture_test.py",
    "tests/smt_test.py",
    "tests/smt_datatype_test.py",
    "tests/recursion_soundness_test.py",
    "tests/refined_match_test.py",
    "tests/typeclass_test.py",
    "tests/package_dependencies_test.py",
]

if __name__ == "__main__":
    raise SystemExit(pytest.main([*CORE_TESTS, *sys.argv[1:]]))
