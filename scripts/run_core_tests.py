"""Fast mandatory cross-version gate; the single full-suite job remains exhaustive."""

import sys

import pytest

CORE_TESTS = [
    "tests/core_properties_test.py",
    "tests/context_snapshot_test.py",
    "tests/parser_locations_test.py",
    "tests/roundtrip_test.py",
    "tests/compilation_session_test.py",
    "tests/compilation_unit_test.py",
    "tests/link_contexts_test.py",
    "tests/backend_test.py",
    "tests/llvm_refinements_test.py::test_nonnegative_parameter_allows_logical_shift_for_floor_division",
    "tests/substitutions_test.py",
    "tests/type_substitution_capture_test.py",
    "tests/smt_test.py",
    "tests/smt_modulo_runtime_test.py",
    "tests/smt_datatype_test.py",
    "tests/recursion_soundness_test.py",
    "tests/polymorphic_subtyping_soundness_test.py",
    "tests/synthesis_list_refinement_soundness_test.py",
    "tests/datatype_relations_test.py",
    "tests/inferred_function_types_test.py",
    "tests/tdsyn_existential_refinements_test.py",
    "tests/theorem_syntax_test.py",
    "tests/precondition_diagnostics_test.py",
    "tests/refined_match_test.py",
    "tests/typeclass_test.py",
    "tests/typeclass_resolution_test.py",
    "tests/typeclass_higher_kinds_test.py",
    "tests/synthesis_typeclasses_test.py::test_generic_convert_across_backends[tdsyn]",
    "tests/synthesis_typeclasses_test.py::test_generic_convert_across_backends[tdsyn_backward]",
    "tests/synthesis_typeclasses_test.py::test_kind_matching_includes_abstract_and_partially_applied_constructors",
    "tests/stdlib_num_test.py",
    "tests/package_dependencies_test.py",
]

if __name__ == "__main__":
    raise SystemExit(pytest.main([*CORE_TESTS, *sys.argv[1:]]))
