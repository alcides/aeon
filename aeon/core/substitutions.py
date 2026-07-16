"""Core substitution and instantiation walks.

All of these are implemented in the Rust core (aeon_rs); this module is a
thin re-export.
"""

from __future__ import annotations

from aeon_rs import instantiate_refinement_in_type as instantiate_refinement_in_type
from aeon_rs import liquefy as liquefy
from aeon_rs import substitute_vartype as substitute_vartype
from aeon_rs import substitute_vartype_in_term as substitute_vartype_in_term
from aeon_rs import substitution as substitution
from aeon_rs import substitution_in_liquid as substitution_in_liquid
from aeon_rs import substitution_in_type as substitution_in_type
from aeon_rs import substitution_liquid_in_type as substitution_liquid_in_type
