"""Horn-clause solver — pure re-export of the Rust core.

Implementation lives in ``aeon-rs/src/horn.rs``. The qualifier-candidate
path used to call back into Python's ``aeon.typechecking.liquid`` and
``aeon.typechecking.qualifiers``; those are now Rust too
(``liquid_check.rs`` / ``qualifiers.rs``), so the call-back path is
Rust-to-Rust end-to-end. The only Python data still read at runtime
is ``aeon.core.liquid_ops.liquid_prelude`` (the built-in operator type
signatures), which stays in Python for now.
"""

from __future__ import annotations

from typing import TypeAlias

from aeon_rs import adapt_qualifier_to_hole as adapt_qualifier_to_hole
from aeon_rs import apply as apply
from aeon_rs import build_qualifier_candidates as build_qualifier_candidates
from aeon_rs import apply_constraint as apply_constraint
from aeon_rs import apply_liquid as apply_liquid
from aeon_rs import build_initial_assignment as build_initial_assignment
from aeon_rs import contains_horn as contains_horn
from aeon_rs import contains_horn_constraint as contains_horn_constraint
from aeon_rs import extract_components_of_imp as extract_components_of_imp
from aeon_rs import fill_horn_arguments as fill_horn_arguments
from aeon_rs import fixpoint as fixpoint
from aeon_rs import flat as flat
from aeon_rs import fresh as fresh
from aeon_rs import get_possible_args as get_possible_args
from aeon_rs import has_k_head as has_k_head
from aeon_rs import merge_assignments as merge_assignments
from aeon_rs import mk_arg as mk_arg
from aeon_rs import obtain_holes as obtain_holes
from aeon_rs import obtain_holes_constraint as obtain_holes_constraint
from aeon_rs import smt_base_type as smt_base_type
from aeon_rs import solve as solve
from aeon_rs import split as split
from aeon_rs import weaken as weaken
from aeon_rs import wellformed_horn as wellformed_horn

from aeon.core.liquid import LiquidTerm
from aeon.utils.name import Name

Assignment: TypeAlias = dict[Name, list[LiquidTerm]]
