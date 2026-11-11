"""Runtime refinement contracts with Findler–Felleisen blame (issue #443)."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable

from aeon.backend.liquid_eval import UninterpretedInLiquid, UnevaluableLiquid, eval_liquid_bool
from aeon.core.liquid import LiquidLiteralBool, LiquidTerm
from aeon.core.terms import Rec, Term
from aeon.core.types import AbstractionType, RefinedType, Type
from aeon.core.types import TypePolymorphism, RefinementPolymorphism
from aeon.errors import ContractViolationError
from aeon.typechecking.context import TypingContext, UninterpretedBinder
from aeon.typechecking.termination import _opened_refinement_liquid
from aeon.utils.location import Location, SynthesizedLocation
from aeon.utils.name import Name


@dataclass
class ContractState:
    """Runtime contract configuration threaded through evaluation."""

    uninterpreted: dict[Name | str, Type]
    runtime: dict[Name | str, Any]
    fn_types: dict[Name, Type]

    @classmethod
    def from_contexts(
        cls, typing_ctx: TypingContext, fn_types: dict[Name, Type], runtime: dict[Name | str, Any]
    ) -> ContractState:
        uninterpreted: dict[Name | str, Type] = {}
        for entry in typing_ctx.entries:
            if isinstance(entry, UninterpretedBinder):
                uninterpreted[entry.name] = entry.type
        return cls(uninterpreted=uninterpreted, runtime=runtime, fn_types=fn_types)


def collect_top_level_fn_types(core: Term) -> dict[Name, Type]:
    out: dict[Name, Type] = {}
    cur: Term = core
    while isinstance(cur, Rec):
        out[cur.var_name] = cur.var_type
        cur = cur.body
    return out


def build_runtime_liquid_env(values: dict[Name, Any]) -> dict[Name | str, Any]:
    """Keep lexical binding identities when registering liquid callables."""
    runtime: dict[Name | str, Any] = {}
    for name, value in values.items():
        if callable(value):
            runtime[name] = value
    return runtime


def register_runtime_callable(state: ContractState, name: Name, value: Any) -> None:
    if callable(value):
        state.runtime[name] = value


def _strip_type_wrappers(ty: Type) -> Type:
    while isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
        ty = ty.body
    return ty


def _check_liquid(
    predicate: LiquidTerm,
    env: dict[Name, Any],
    state: ContractState,
    *,
    blame: str,
    callee: Name | None,
    loc: Location | None,
) -> None:
    if predicate == LiquidLiteralBool(True):
        return
    try:
        ok = eval_liquid_bool(predicate, env, uninterpreted=state.uninterpreted, runtime=state.runtime)
    except UninterpretedInLiquid:
        return
    except UnevaluableLiquid:
        return
    if not ok:
        where = callee.name if callee is not None else "<unknown>"
        raise ContractViolationError(
            blame=blame,
            binding=where,
            predicate=predicate,
            loc=loc or SynthesizedLocation("contracts"),
        )


def check_param_refinement(
    param_type: Type,
    param_name: Name,
    value: Any,
    state: ContractState,
    *,
    callee: Name,
    loc: Location | None,
    env: dict[Name, Any] | None = None,
) -> None:
    param_type = _strip_type_wrappers(param_type)
    if not isinstance(param_type, RefinedType):
        return
    opened = _opened_refinement_liquid(param_type, param_name, [param_name], [param_name])
    if opened is None:
        return
    env = {**(env or {}), param_name: value}
    _check_liquid(opened, env, state, blame="caller", callee=callee, loc=loc)


def check_return_refinement(
    return_type: Type,
    value: Any,
    state: ContractState,
    *,
    callee: Name,
    loc: Location | None,
    env: dict[Name, Any] | None = None,
) -> None:
    return_type = _strip_type_wrappers(return_type)
    if not isinstance(return_type, RefinedType):
        return
    env = {**(env or {}), return_type.name: value}
    _check_liquid(return_type.refinement, env, state, blame="callee", callee=callee, loc=loc)


@dataclass
class ContractClosure:
    """Callable wrapper that checks curried refinements at run time."""

    fn: Callable[[Any], Any]
    arrow_type: Type
    callee: Name
    state: ContractState
    loc: Location | None = None
    env: dict[Name, Any] = field(default_factory=dict)

    def __call__(self, arg: Any) -> Any:
        ty = _strip_type_wrappers(self.arrow_type)
        if isinstance(ty, AbstractionType):
            env = {**self.env, ty.var_name: arg}
            check_param_refinement(ty.var_type, ty.var_name, arg, self.state, callee=self.callee, loc=self.loc, env=env)
            result = self.fn(arg)
            rest = _strip_type_wrappers(ty.type)
            if isinstance(rest, AbstractionType):
                return ContractClosure(result, rest, self.callee, self.state, loc=self.loc, env=env)
            check_return_refinement(rest, result, self.state, callee=self.callee, loc=self.loc, env=env)
            return result
        result = self.fn(arg)
        check_return_refinement(ty, result, self.state, callee=self.callee, loc=self.loc, env=self.env)
        return result


def wrap_callable(
    fn: Callable[[Any], Any],
    fn_type: Type,
    callee: Name,
    state: ContractState,
    *,
    loc: Location | None = None,
    env: dict[Name, Any] | None = None,
) -> ContractClosure:
    return ContractClosure(fn, fn_type, callee, state, loc=loc, env=dict(env or {}))
