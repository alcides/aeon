"""Sugar → core desugaring pipeline — pure re-export of the Rust core.

The full pipeline (algorithmic transforms *and* orchestration —
imports, decorator macro pass, the top-level :func:`desugar` driver)
lives in Rust now. The parser and the decorator macro system remain
Python; Rust calls back into them via FFI at the appropriate points.
"""

from __future__ import annotations

from aeon_rs import (
    DesugaredProgram,
    _bare_name,
    _is_native_import_def,
    _resolve_import,
    apply_decorators_in_definitions,
    apply_decorators_in_program,
    clear_import_cache,
    convert_definition_to_srec,
    definition_with_inferred_decreasing,
    desugar,
    determine_main_function,
    expand_inductive_decls,
    infer_inductive_rforall_decls,
    introduce_forall_in_types,
    introduce_rforall_in_types,
    lower_by_blocks_in_definitions,
    lower_by_blocks_in_sterm,
    lower_match_to_inductive_rec,
    py_handle_imports as handle_imports,
    replace_concrete_types,
    resolve_qualified_names_in_definition,
    resolve_qualified_names_in_sterm,
    resolve_qualified_names_in_stype,
    type_of_definition,
    update_program_and_context,
)
from aeon.utils.name import Name

# Scope-type aliases (kept for compatibility with external code/tests).
ModuleScope = dict[str, Name]
QualifiedScope = dict[tuple[str, str], Name]
UnqualifiedScope = dict[str, Name]

__all__ = [
    "DesugaredProgram",
    "ModuleScope",
    "QualifiedScope",
    "UnqualifiedScope",
    "_bare_name",
    "_is_native_import_def",
    "_resolve_import",
    "apply_decorators_in_definitions",
    "apply_decorators_in_program",
    "clear_import_cache",
    "convert_definition_to_srec",
    "definition_with_inferred_decreasing",
    "desugar",
    "determine_main_function",
    "expand_inductive_decls",
    "handle_imports",
    "infer_inductive_rforall_decls",
    "introduce_forall_in_types",
    "introduce_rforall_in_types",
    "lower_by_blocks_in_definitions",
    "lower_by_blocks_in_sterm",
    "lower_match_to_inductive_rec",
    "replace_concrete_types",
    "resolve_qualified_names_in_definition",
    "resolve_qualified_names_in_sterm",
    "resolve_qualified_names_in_stype",
    "type_of_definition",
    "update_program_and_context",
]
