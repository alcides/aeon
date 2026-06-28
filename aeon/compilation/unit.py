from __future__ import annotations

from dataclasses import dataclass, field

from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.decorators import Metadata
from aeon.sugar.program import ClassDecl, InductiveDecl, InstanceDecl, TypeDecl
from aeon.sugar.stypes import SType
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

# Bump when the on-disk .aec layout or semantics change.
AEC_FORMAT_VERSION = 1


@dataclass(frozen=True)
class ModuleExport:
    """A public binding from a compilation unit."""

    bare_name: str
    internal_name: Name
    sugar_type: SType
    core_type: Type


@dataclass
class CompiledUnit:
    """Trusted compilation artifact for a single .ae module."""

    format_version: int
    compiler_version: str
    module_path: str
    source_path: str
    source_hash: str

    # Core IR for this module's own definitions (Rec chain ending in the module tail).
    core_spine: Term
    typing_ctx: TypingContext
    metadata: Metadata

    # Surface metadata needed when compiling importers.
    type_decls: list[TypeDecl]
    inductive_decls: list[InductiveDecl]
    class_decls: list[ClassDecl]
    instance_decls: list[InstanceDecl]
    constructor_to_type: dict[str, Name]
    constructor_defs: dict[str, Name]

    exports: dict[str, ModuleExport]
    qualified_scope: dict[tuple[str, str], Name]

    dependencies: list[str]  # module_path strings of direct imports
    trusted_names: frozenset[Name] = field(default_factory=frozenset)
    # Decorator metadata before the core phase runs (includes the core-phase queue).
    source_metadata: Metadata = field(default_factory=dict)

    def dependency_hashes(self) -> dict[str, str]:
        return {dep: "" for dep in self.dependencies}
