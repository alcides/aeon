"""Macro-expand abstract set membership before it reaches Z3.

``Set Int`` and ``Set Bool`` stay Z3 sets. An abstract element sort is not
given a ``SetSort``: ``cup``, ``dif``, ``cap``, ``sng`` and ``empty`` are
rewritten to boolean combinations of membership, and ``x = y`` inside a
singleton is the element equality the rest of the VC already uses. A set
equation becomes extensional equality at one fresh element, which is sound
for the quantifier-free fragment and enough for ``elems`` preservation.
"""

from __future__ import annotations

from collections.abc import Mapping

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidTerm, LiquidVar
from aeon.core.types import (
    AbstractionType,
    RefinementPolymorphism,
    RefinedType,
    Type,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
    t_bool,
    t_int,
)
from aeon.utils.name import Name
from aeon.verification.smt_datatypes import strip_binder_id

_SET_BUILDERS = frozenset({"Set_empty", "Set_sng", "Set_cup", "Set_cap", "Set_dif"})
_CONCRETE_ELEMENTS = frozenset({"Int", "Bool"})


def _base(ty: Type) -> Type:
    if isinstance(ty, RefinedType):
        return _base(ty.type)
    if isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
        return _base(ty.body)
    return ty


def _lookup(mapping: Mapping[str, object], name: Name) -> object | None:
    for key in (str(name), strip_binder_id(str(name)), name.name):
        if key in mapping:
            return mapping[key]
    return None


def set_element(ty: Type | None) -> tuple[str, Type] | None:
    """``("z3", elem)`` for a Z3 set, ``("abs", elem)`` for a macro set."""
    if ty is None:
        return None
    ty = _base(ty)
    if not isinstance(ty, TypeConstructor) or ty.name.name != "Set":
        return None
    if not ty.args:
        return ("z3", t_int)
    element = _base(ty.args[0])
    if isinstance(element, TypeConstructor) and not element.args and element.name.name in _CONCRETE_ELEMENTS:
        return ("z3", element)
    return ("abs", element if isinstance(element, (TypeConstructor, TypeVar)) else t_int)


def _substitute(ty: Type, subst: dict[Name, Type]) -> Type:
    ty = _base(ty)
    match ty:
        case TypeVar(name) if name in subst:
            return subst[name]
        case TypeConstructor(name, args):
            return TypeConstructor(name, [_substitute(arg, subst) for arg in args], refinements=ty.refinements)
        case _:
            return ty


def _unify(actual: Type, expected: Type, subst: dict[Name, Type]) -> None:
    actual, expected = _base(actual), _base(expected)
    if isinstance(expected, TypeVar):
        subst.setdefault(expected.name, actual)
        return
    if isinstance(actual, TypeVar):
        subst.setdefault(actual.name, expected)
        return
    if (
        isinstance(actual, TypeConstructor)
        and isinstance(expected, TypeConstructor)
        and actual.name.name == expected.name.name
        and len(actual.args) == len(expected.args)
    ):
        for left, right in zip(actual.args, expected.args):
            _unify(left, right, subst)


def _apply(fun_ty: Type, arguments: list[Type]) -> Type | None:
    subst: dict[Name, Type] = {}
    current: Type = fun_ty
    while isinstance(current, (TypePolymorphism, RefinementPolymorphism)):
        current = current.body
    for argument in arguments:
        if not isinstance(current, AbstractionType):
            return None
        _unify(argument, current.var_type, subst)
        current = current.type
    if isinstance(current, AbstractionType):
        return None
    return _substitute(_base(current), subst)


class _Env:
    def __init__(self, variables: Mapping[str, TypeConstructor], functions: Mapping[str, Type]) -> None:
        self.variables = variables
        self.functions = functions

    def typeof(self, term: LiquidTerm) -> Type | None:
        match term:
            case LiquidVar(name) if name.name == "Set_empty":
                # The prelude schema is polymorphic. An uninstantiated empty
                # set is the integer set until an abstract argument joins it.
                return TypeConstructor(Name("Set", 0), [])
            case LiquidVar(name):
                found = _lookup(self.variables, name)
                if isinstance(found, Type):
                    return found
                found = _lookup(self.functions, name)
                if isinstance(found, Type):
                    return _apply(found, []) or found
                return None
            case LiquidApp(fun, args):
                arg_types = [self.typeof(arg) for arg in args]
                if fun.name in _SET_BUILDERS or fun.name == "Set_mem":
                    return _set_operator_type(fun.name, arg_types)
                found = _lookup(self.functions, fun)
                if isinstance(found, Type) and all(ty is not None for ty in arg_types):
                    return _apply(found, [ty for ty in arg_types if ty is not None])
                return None
            case _:
                return None


def _set_operator_type(name: str, arg_types: list[Type | None]) -> Type | None:
    if name == "Set_empty":
        return TypeConstructor(Name("Set", 0), [])
    if name == "Set_sng":
        element = arg_types[0] if arg_types else None
        if element is None:
            return TypeConstructor(Name("Set", 0), [])
        return TypeConstructor(Name("Set", 0), [_base(element)])
    if name in {"Set_cup", "Set_cap", "Set_dif"}:
        concrete: Type | None = None
        for argument in arg_types:
            kind = set_element(argument)
            if kind is None:
                continue
            if kind[0] == "abs":
                return argument
            concrete = concrete or argument
        return concrete if concrete is not None else TypeConstructor(Name("Set", 0), [])
    if name == "Set_mem":
        return t_bool
    return None


def _abstract(env: _Env, term: LiquidTerm) -> bool:
    kind = set_element(env.typeof(term))
    return kind is not None and kind[0] == "abs"


def _element_carrier(element: Type) -> TypeConstructor:
    element = _base(element)
    if isinstance(element, TypeVar):
        return TypeConstructor(element.name)
    if isinstance(element, TypeConstructor):
        return element
    return t_int


def _eq(left: LiquidTerm, right: LiquidTerm) -> LiquidTerm:
    return LiquidApp(Name("==", 0), [left, right])


def _and(left: LiquidTerm, right: LiquidTerm) -> LiquidTerm:
    return LiquidApp(Name("&&", 0), [left, right])


def _or(left: LiquidTerm, right: LiquidTerm) -> LiquidTerm:
    return LiquidApp(Name("||", 0), [left, right])


def _not(term: LiquidTerm) -> LiquidTerm:
    return LiquidApp(Name("!", 0), [term])


def _expand_mem(element: LiquidTerm, container: LiquidTerm) -> LiquidTerm:
    match container:
        case LiquidVar(name) if name.name == "Set_empty":
            return LiquidLiteralBool(False)
        case LiquidApp(fun, args) if fun.name == "Set_empty":
            return LiquidLiteralBool(False)
        case LiquidApp(fun, args) if fun.name == "Set_cup" and len(args) == 2:
            return _or(_expand_mem(element, args[0]), _expand_mem(element, args[1]))
        case LiquidApp(fun, args) if fun.name == "Set_cap" and len(args) == 2:
            return _and(_expand_mem(element, args[0]), _expand_mem(element, args[1]))
        case LiquidApp(fun, args) if fun.name == "Set_dif" and len(args) == 2:
            return _and(_expand_mem(element, args[0]), _not(_expand_mem(element, args[1])))
        case LiquidApp(fun, args) if fun.name == "Set_sng" and len(args) == 1:
            return _eq(element, args[0])
        case _:
            return LiquidApp(Name("Set_mem", 0), [element, container])


def _expand(term: LiquidTerm, env: _Env, skolem: LiquidVar) -> LiquidTerm:
    match term:
        case LiquidApp(fun, args) if (
            fun.name in {"==", "!="} and len(args) == 2 and (_abstract(env, args[0]) or _abstract(env, args[1]))
        ):
            same = _eq(_expand_mem(skolem, args[0]), _expand_mem(skolem, args[1]))
            return same if fun.name == "==" else _not(same)
        case LiquidApp(fun, args) if fun.name == "Set_mem" and len(args) == 2 and _abstract(env, args[1]):
            return _expand_mem(args[0], args[1])
        case LiquidApp(fun, args):
            expanded = [_expand(arg, env, skolem) for arg in args]
            if all(new is old for new, old in zip(expanded, args)):
                return term
            return LiquidApp(fun, expanded, loc=term.loc)
        case _:
            return term


def expand_abstract_sets(
    premise: LiquidTerm,
    conclusion: LiquidTerm,
    variables: Mapping[str, TypeConstructor],
    functions: Mapping[str, Type],
) -> tuple[LiquidTerm, LiquidTerm, dict[str, TypeConstructor]]:
    """Rewrite abstract set formulas. Concrete integer sets are returned unchanged."""
    env = _Env(variables, functions)
    skolem_name = Name("__aeon_set_elem", 0)
    skolem = LiquidVar(skolem_name)
    new_premise = _expand(premise, env, skolem)
    new_conclusion = _expand(conclusion, env, skolem)
    if new_premise is premise and new_conclusion is conclusion:
        return premise, conclusion, {}
    element = _element_of_expanded(premise, conclusion, env) or t_int
    return new_premise, new_conclusion, {str(skolem_name): _element_carrier(element)}


def _element_of_expanded(premise: LiquidTerm, conclusion: LiquidTerm, env: _Env) -> Type | None:
    pending = [premise, conclusion]
    while pending:
        term = pending.pop()
        kind = set_element(env.typeof(term))
        if kind is not None and kind[0] == "abs":
            return kind[1]
        if isinstance(term, LiquidApp):
            pending.extend(term.args)
    return None
