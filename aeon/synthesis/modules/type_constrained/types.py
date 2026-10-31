"""Ordinary types and the bridge back to Aeon's session-local compiler.

No inference/model dependency belongs in this module. Refinements are erased
only for prefix search; the synthesizer retains the original acceptance gate.
"""

from __future__ import annotations

from dataclasses import dataclass
import re

from aeon.compilation.session import current_session
from aeon.core.instantiation import type_substitution
from aeon.core.multiplicity import MN, MOmega
from aeon.core.terms import Term
from aeon.core.types import AbstractionType, RefinedType, Type, TypeConstructor, TypePolymorphism
from aeon.decorators.api import Metadata
from aeon.elaboration import elaborate
from aeon.elaboration.context import ElaborationTypingContext, ElabVariableBinder
from aeon.sugar.bind import bind_sterm
from aeon.sugar.lifting import lift_type
from aeon.sugar.lowering import lower_to_core
from aeon.sugar.parser import parse_expression
from aeon.sugar.name_resolution import resolve_qualified_names_in_sterm
from aeon.synthesis.api import UnsupportedSynthesisGoal
from aeon.synthesis.scope import fitness_relevant_names, without_excluded_names
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


@dataclass(frozen=True)
class Mono:
    name: str
    arg: Mono | None = None
    result: Mono | None = None

    def core(self) -> Type:
        if self.arg is not None and self.result is not None:
            return AbstractionType(Name("_arg", 0), self.arg.core(), self.result.core())
        return TypeConstructor(Name(self.name, 0))


BASES = tuple(Mono(n) for n in ("Int", "Bool", "String", "Float", "Unit"))
INT, BOOL, STRING, FLOAT, UNIT = BASES
OPERATORS = {"+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "!=", "&&", "||", "-->", "!"}
IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z")
KEYWORDS = {"let", "in", "if", "then", "else", "fun", "true", "false", "match", "with", "by", "end"}


def ordinary(ty: Type, *, primitive: bool = False) -> Mono:
    if isinstance(ty, RefinedType):
        return ordinary(ty.type, primitive=primitive)
    if isinstance(ty, TypeConstructor) and not ty.args and ty.name.id == 0 and ty.name.name in {t.name for t in BASES}:
        return Mono(ty.name.name)
    if isinstance(ty, AbstractionType):
        if ty.multiplicity is not MOmega and not (primitive and ty.multiplicity is MN):
            raise UnsupportedSynthesisGoal("llm_type_constrained supports only unrestricted arrows")
        return Mono("->", ordinary(ty.var_type, primitive=primitive), ordinary(ty.type, primitive=primitive))
    raise UnsupportedSynthesisGoal(
        f"llm_type_constrained needs monomorphic Int/Bool/String/Float/Unit or unrestricted arrows; got {ty}"
    )


def subtypes(ty: Mono) -> set[Mono]:
    return {ty} | (subtypes(ty.arg) | subtypes(ty.result) if ty.arg is not None and ty.result is not None else set())


class Scope:
    """A fixed lexical environment. Its caches must never escape this object."""

    def __init__(
        self, ctx: TypingContext, expected: Type, fun_name: Name | None = None, metadata: Metadata | None = None
    ):
        self.session = current_session()
        self.expected = ordinary(expected)
        self.original_expected = expected
        self.ctx = ctx
        self.bindings: dict[str, tuple[Name, Type]] = {}
        self.environment: tuple[tuple[str, Mono], ...]
        env: list[tuple[str, Mono]] = []
        hidden = fitness_relevant_names(metadata or {})
        for name, ty in without_excluded_names(ctx).concrete_vars():
            if name == fun_name or name.name in hidden:
                continue
            primitive = name.id == 0 and name.name in OPERATORS
            if not primitive and (not IDENTIFIER.fullmatch(name.name) or name.name in KEYWORDS):
                continue
            if name.name.startswith(("true.", "false.")):
                continue  # Aeon lexes these as literal receivers, not qualified variables.
            candidates = [ty]
            if primitive and isinstance(ty, TypePolymorphism):
                domains = (INT, FLOAT, BOOL, STRING) if name.name in {"==", "!="} else (INT, FLOAT)
                candidates = [type_substitution(ty.body, ty.name, t.core()) for t in domains]
            supported = []
            for candidate in candidates:
                try:
                    supported.append(ordinary(candidate, primitive=primitive))
                except UnsupportedSynthesisGoal:
                    pass  # Unsupported components are absent, never approximated.
            if supported:
                self.bindings[name.name] = (name, ty)
                env.extend((name.name, t) for t in supported)
        self.environment = tuple(env)
        self.universe = tuple(
            sorted(set(BASES) | subtypes(self.expected) | {t for _, ty in env for t in subtypes(ty)}, key=repr)
        )

    def compile(self, source: str) -> Term:
        """Parse, resolve, bind and elaborate in the *original* session/scope.

        Elaboration inserts type applications for primitive operators. Existing
        free names retain their IDs; new let/lambda binders are hygienic.
        """
        with self.session.activate():
            qualified: dict[tuple[str, str], Name] = {}
            for spelling, (name, _) in self.bindings.items():
                if "." in spelling:
                    qualifier, bare = spelling.rsplit(".", 1)
                    qualified[qualifier, bare] = name
            term = resolve_qualified_names_in_sterm(parse_expression(source), qualified, {})
            term = bind_sterm(term, [(spelling, name) for spelling, (name, _) in self.bindings.items()])
            context = ElaborationTypingContext(
                [ElabVariableBinder(name, lift_type(ty)) for name, ty in self.bindings.values()]
            )
            return lower_to_core(elaborate(context, term, lift_type(self.expected.core())))
