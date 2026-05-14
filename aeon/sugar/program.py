"""Surface (sugar) AST: STerm hierarchy + the Node declaration hierarchy.

Re-exports the Rust core (aeon_rs). The classes mirror what was previously
defined here as Python dataclasses.
"""

from __future__ import annotations

from aeon_rs import Decorator as Decorator
from aeon_rs import Definition as Definition
from aeon_rs import ImportAe as ImportAe
from aeon_rs import InductiveDecl as InductiveDecl
from aeon_rs import Node as Node
from aeon_rs import Program as Program
from aeon_rs import SAbstraction as SAbstraction
from aeon_rs import SAnnotation as SAnnotation
from aeon_rs import SAnonConstructor as SAnonConstructor
from aeon_rs import SApplication as SApplication
from aeon_rs import SBy as SBy
from aeon_rs import SHole as SHole
from aeon_rs import SIf as SIf
from aeon_rs import SLet as SLet
from aeon_rs import SLiteral as SLiteral
from aeon_rs import SMatch as SMatch
from aeon_rs import SMatchBranch as SMatchBranch
from aeon_rs import SQualifiedVar as SQualifiedVar
from aeon_rs import SRec as SRec
from aeon_rs import SRefinementAbstraction as SRefinementAbstraction
from aeon_rs import SRefinementApplication as SRefinementApplication
from aeon_rs import STerm as STerm
from aeon_rs import STypeAbstraction as STypeAbstraction
from aeon_rs import STypeApplication as STypeApplication
from aeon_rs import SVar as SVar
from aeon_rs import TypeDecl as TypeDecl
