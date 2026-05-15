"""Verification-condition constraints — Constraint hierarchy + alpha-equivalent
canonical key + free-variable helpers. Re-exports the Rust core (aeon_rs).
"""

from __future__ import annotations

from aeon_rs import Conjunction as Conjunction
from aeon_rs import Constraint as Constraint
from aeon_rs import Implication as Implication
from aeon_rs import LiquidConstraint as LiquidConstraint
from aeon_rs import ReflectedFunctionDeclaration as ReflectedFunctionDeclaration
from aeon_rs import TypeVarDeclaration as TypeVarDeclaration
from aeon_rs import UninterpretedFunctionDeclaration as UninterpretedFunctionDeclaration
from aeon_rs import alpha_key as alpha_key
from aeon_rs import variables_free_in as variables_free_in
from aeon_rs import variables_in_liq as variables_in_liq
