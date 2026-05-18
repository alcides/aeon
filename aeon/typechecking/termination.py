"""Termination metric constraints — pure re-export of the Rust core
(``aeon-rs/src/termination.rs``)."""

from __future__ import annotations

from aeon_rs import _lexicographic_less as _lexicographic_less
from aeon_rs import _liquefy_metric_at as _liquefy_metric_at
from aeon_rs import collect_recursive_calls_with_paths as collect_recursive_calls_with_paths
from aeon_rs import entry_refinement_liquids as entry_refinement_liquids
from aeon_rs import peel_abstractions as peel_abstractions
from aeon_rs import peel_application_chain as peel_application_chain
from aeon_rs import peel_type_formal_names as peel_type_formal_names
from aeon_rs import substitute_formals as substitute_formals
from aeon_rs import termination_metric_constraints as termination_metric_constraints
