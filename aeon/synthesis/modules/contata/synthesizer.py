"""``-s contata`` — the example-driven Constraint-Annotated Tree Automaton.

Where the ``cata`` backend discharges a *refinement-type* spec one candidate at
a time with the liquid typechecker, ``contata`` is the paper-faithful **version
space**: a candidate body denotes (symbolically, over the functions under
synthesis as uninterpreted functions) and is accepted under an SMT model against
the ground ``@example`` spec, with the well-foundedness side condition and
MinTree extraction (see :mod:`aeon.synthesis.modules.contata.cata`).

This adapter wires that version space into the single-hole ``Synthesizer`` API:
it reads the hole's ``@example`` I/O facts, runs :func:`synthesize_group` for the
one member, maps the resulting DSL body onto the real in-scope names
(parameter, the recursive self-call, and the arithmetic/comparison operators),
and discharges the mapped term through ``validate`` as a final soundness gate.
A whole ``mutual`` block is co-synthesised jointly by the entrypoint
(:func:`aeon.synthesis.entrypoint._cosynthesize_group`); this backend is the
per-member engine that path drives.
"""

from __future__ import annotations

from typing import Any, Callable, Optional

from loguru import logger

from aeon.core.terms import Application, If, Literal, Term, Var
from aeon.core.types import Type, t_bool, t_int
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer, SynthesisNotSuccessful
from aeon.synthesis.modules.fta.synthesizer import _safe
from aeon.synthesis.modules.contata.cata import (
    BOOL,
    INT,
    Example,
    MemberSig,
    _PARAM,
    synthesize_group,
)
from aeon.synthesis.modules.lta.polymorphism import is_polymorphic, monomorphize
from aeon.synthesis.modules.symetric.synthesizer import base_key
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name

_loc = SynthesizedLocation("contata")


class ContataSynthesizer(Synthesizer):
    """Example-driven CATA version space, single-hole adapter."""

    def __init__(self, max_size: int = 4):
        self.max_size = max_size

    def computations(self, primitives: Any) -> dict[str, Any]:
        # Acceptance is by the SMT version space + ``validate``, not by a fitness
        # value over a single ground input. Nothing extra to compute.
        return {}

    def synthesize(
        self,
        ctx: TypingContext,
        type: Type,
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        fun_name: Name,
        metadata: Metadata,
        budget: float = 60,
        ui: SynthesisUI = SynthesisUI(),
        output_value: Callable[[Term], object] | None = None,
    ) -> Term:
        ui.register(None, None, 0, True)
        entry = metadata.get(fun_name, {})
        io_examples = entry.get("io_examples", [])
        io_params = entry.get("io_params", [])

        # The version space synthesises *unary* members from a ground spec.
        if not io_examples:
            raise SynthesisNotSuccessful(
                f"contata: no @example I/O facts for {fun_name.name}; this backend synthesises from "
                "ground examples (e.g. @example(f 0 = true))."
            )
        if len(io_params) != 1:
            raise SynthesisNotSuccessful(
                f"contata: {fun_name.name} is not unary ({len(io_params)} value parameters); the "
                "version space currently handles single-argument members."
            )
        param_name = io_params[0]

        arg_key = _dsl_type(self._param_type(ctx, param_name))
        ret_key = _dsl_type(type)
        if arg_key is None or ret_key is None:
            raise SynthesisNotSuccessful(
                f"contata: {fun_name.name} has a type outside the Int/Bool DSL; not supported."
            )

        examples: list[Example] = []
        for args, out in io_examples:
            if len(args) != 1:
                raise SynthesisNotSuccessful("contata: expected exactly one argument per example.")
            examples.append(Example(fun_name.name, args[0], out))

        members = [MemberSig(fun_name.name, arg_key, ret_key)]
        result = synthesize_group(members, examples, max_size=self.max_size)
        if result is None:
            raise SynthesisNotSuccessful(
                f"contata: no example-consistent body for {fun_name.name} within size {self.max_size}."
            )

        op_names = _operator_names(ctx)
        body = _to_core(result.bodies[fun_name.name], param_name, fun_name, op_names)
        if body is None:
            raise SynthesisNotSuccessful(
                f"contata: synthesised body uses an operator not in scope for {fun_name.name}."
            )
        if not _safe(validate, body):
            raise SynthesisNotSuccessful(
                f"contata: synthesised body for {fun_name.name} did not discharge against its type."
            )
        ui.register(body, [0.0], 0, True)
        logger.log(
            "SYNTHESIZER",
            f"contata: version-space body for {fun_name.name} accepted under SMT over "
            f"{len(examples)} example(s) and discharged by the typechecker.",
        )
        return body

    @staticmethod
    def _param_type(ctx: TypingContext, param_name: Name) -> Optional[Type]:
        for n, ty in ctx.vars():
            if n == param_name:
                return ty
        return None


def _dsl_type(ty: Optional[Type]) -> Optional[str]:
    """The DSL key for an Aeon type, or ``None`` if outside the supported fragment."""
    if ty is None:
        return None
    key = base_key(ty)
    if key == base_key(t_int):
        return INT
    if key == base_key(t_bool):
        return BOOL
    return None


def _operator_names(ctx: TypingContext) -> dict[str, Term]:
    """Map each DSL operator string to a concrete in-scope **head term**. The
    prelude's arithmetic/comparison operators are polymorphic (``forall a:B, …``),
    so the bare ``Var`` the version space emits will not typecheck — each is
    monomorphised at ``Int`` (a ``TypeApplication`` nest), exactly as the ``cata``
    backend does, so ``x == 0`` / ``x - 1`` discharge."""
    wanted = {"+", "-", "==", "<", "<=", ">", ">="}
    found: dict[str, Term] = {}
    for n, ty in ctx.vars():
        if n.name not in wanted or n.name in found:
            continue
        if is_polymorphic(ty):
            insts = monomorphize(n, ty, [t_int], max_instantiations=4)
            if insts:
                found[n.name] = insts[0].term
        else:
            found[n.name] = Var(n)
    return found


def _to_core(term: Term, param_name: Name, fun_name: Name, op_names: dict[str, Term]) -> Optional[Term]:
    """Rebind the version-space body's id-0 placeholder names to the real ones:
    the parameter, the recursive self-call, and the (monomorphised) operators.
    Returns ``None`` if an operator is not in scope."""
    match term:
        case Literal(_, _):
            return term
        case Var(name) if name == _PARAM:
            return Var(param_name)
        case Var(name) if name.name == fun_name.name:
            return Var(fun_name)
        case Var(name):
            return op_names.get(name.name)
        case Application(fun, arg):
            f = _to_core(fun, param_name, fun_name, op_names)
            a = _to_core(arg, param_name, fun_name, op_names)
            return Application(f, a, _loc) if f is not None and a is not None else None
        case If(c, th, el):
            cc = _to_core(c, param_name, fun_name, op_names)
            tt = _to_core(th, param_name, fun_name, op_names)
            ee = _to_core(el, param_name, fun_name, op_names)
            if cc is None or tt is None or ee is None:
                return None
            return If(cc, tt, ee, _loc)
        case _:
            return None
