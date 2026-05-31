from __future__ import annotations

from dataclasses import dataclass
from typing import Generator

from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralFloat
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.types import AbstractionType, RefinedType, RefinementPolymorphism, Top, Type, TypePolymorphism, TypeVar
from aeon.core.types import TypeConstructor
from aeon.utils.location import Location
from aeon.utils.name import Name


class Constraint:
    pass


@dataclass
class LiquidConstraint(Constraint):
    expr: LiquidTerm
    loc: Location | None = None

    def __repr__(self):
        return repr(self.expr)


@dataclass
class Conjunction(Constraint):
    c1: Constraint
    c2: Constraint
    loc: Location | None = None

    def __repr__(self):
        return f"({self.c1}) ∧ ({self.c2})"


@dataclass
class UninterpretedFunctionDeclaration(Constraint):
    name: Name
    type: AbstractionType
    seq: Constraint

    def __repr__(self):
        return f"fun {self.name}:{self.type} => {self.seq}"


@dataclass
class ReflectedFunctionDeclaration(Constraint):
    name: Name
    type: AbstractionType
    params: tuple[Name, ...]
    body: LiquidTerm
    seq: Constraint

    def __repr__(self):
        params = ", ".join(str(p) for p in self.params)
        return f"reflected {self.name}({params}):{self.type} = {self.body} => {self.seq}"


@dataclass
class Implication(Constraint):
    name: Name
    base: TypeConstructor | TypeVar | Top
    pred: LiquidTerm
    seq: Constraint
    loc: Location | None = None

    def __post_init__(self):
        assert isinstance(self.name, Name)

    def __repr__(self):
        return f"∀{self.name}:{self.base}, ({self.pred}) => {self.seq}"


@dataclass
class TypeVarDeclaration(Constraint):
    name: Name
    seq: Constraint

    def __repr__(self):
        return f"type {self.name}, {self.seq}"


def _alpha_name(name: Name, env: dict[tuple[str, int], int], counter: list[int]) -> str:
    """Return a canonical string for a Name, normalizing fresh ids."""
    key = (name.name, name.id)
    if key in env:
        return f"{name.name}#{env[key]}"
    # Not a bound variable — keep original representation
    return str(name)


def _alpha_bind(
    name: Name, env: dict[tuple[str, int], int], counter: list[int]
) -> tuple[str, dict[tuple[str, int], int]]:
    """Bind a name in the alpha-normalization environment, returning its canonical string and new env."""
    key = (name.name, name.id)
    canonical_id = counter[0]
    counter[0] += 1
    new_env = {**env, key: canonical_id}
    return f"{name.name}#{canonical_id}", new_env


def _alpha_liquid(t: LiquidTerm, env: dict[tuple[str, int], int], counter: list[int]) -> str:
    """Alpha-normalize a LiquidTerm to a canonical string."""
    if isinstance(t, LiquidLiteralBool):
        return str(t.value).lower()
    elif isinstance(t, LiquidLiteralInt):
        return str(t.value)
    elif isinstance(t, LiquidLiteralFloat):
        return str(t.value)
    elif isinstance(t, LiquidLiteralString):
        return repr(t.value)
    elif isinstance(t, LiquidVar):
        return _alpha_name(t.name, env, counter)
    elif isinstance(t, LiquidApp):
        fun_s = _alpha_name(t.fun, env, counter)
        if all(not c.isalnum() for c in t.fun.name) and len(t.args) == 2:
            a1 = _alpha_liquid(t.args[0], env, counter)
            a2 = _alpha_liquid(t.args[1], env, counter)
            return f"({a1} {fun_s} {a2})"
        args_s = ",".join(_alpha_liquid(a, env, counter) for a in t.args)
        return f"{fun_s}({args_s})"
    else:
        # LiquidLiteralFloat, LiquidHornApplication, etc.
        return repr(t)


def _alpha_type(ty: Type, env: dict[tuple[str, int], int], counter: list[int]) -> str:
    """Alpha-normalize a Type to a canonical string."""
    if isinstance(ty, AbstractionType):
        var_s, new_env = _alpha_bind(ty.var_name, env, counter)
        vt_s = _alpha_type(ty.var_type, new_env, counter)
        body_s = _alpha_type(ty.type, new_env, counter)
        return f"({var_s}:{vt_s}) -> {body_s}"
    elif isinstance(ty, RefinedType):
        var_s, new_env = _alpha_bind(ty.name, env, counter)
        base_s = _alpha_type(ty.type, new_env, counter)
        ref_s = _alpha_liquid(ty.refinement, new_env, counter)
        return f"{{{var_s}:{base_s} | {ref_s}}}"
    elif isinstance(ty, TypeConstructor):
        if ty.args:
            args_s = " ".join(_alpha_type(a, env, counter) for a in ty.args)
            return f"{ty.name} {args_s}"
        return str(ty.name)
    elif isinstance(ty, TypeVar):
        return _alpha_name(ty.name, env, counter)
    elif isinstance(ty, Top):
        return "⊤"
    elif isinstance(ty, TypePolymorphism):
        var_s, new_env = _alpha_bind(ty.name, env, counter)
        body_s = _alpha_type(ty.body, new_env, counter)
        return f"forall {var_s}:{ty.kind}, {body_s}"
    elif isinstance(ty, RefinementPolymorphism):
        var_s, new_env = _alpha_bind(ty.name, env, counter)
        sort_s = _alpha_type(ty.sort, new_env, counter)
        body_s = _alpha_type(ty.body, new_env, counter)
        return f"forall <{var_s}:{sort_s} -> Bool>, {body_s}"
    else:
        return repr(ty)


def alpha_key(c: Constraint) -> str:
    """Compute an alpha-equivalent canonical string for a constraint.

    Bound variable names are normalized to sequential ids so that
    constraints differing only in fresh variable numbering produce
    the same key.
    """
    env: dict[tuple[str, int], int] = {}
    counter = [0]
    return _alpha_constraint(c, env, counter)


def _alpha_constraint(c: Constraint, env: dict[tuple[str, int], int], counter: list[int]) -> str:
    if isinstance(c, LiquidConstraint):
        return _alpha_liquid(c.expr, env, counter)
    elif isinstance(c, Conjunction):
        left = _alpha_constraint(c.c1, env, counter)
        right = _alpha_constraint(c.c2, env, counter)
        return f"({left}) ∧ ({right})"
    elif isinstance(c, Implication):
        var_s, new_env = _alpha_bind(c.name, env, counter)
        base_s = _alpha_type(c.base, new_env, counter)
        pred_s = _alpha_liquid(c.pred, new_env, counter)
        seq_s = _alpha_constraint(c.seq, new_env, counter)
        return f"∀{var_s}:{base_s}, ({pred_s}) => {seq_s}"
    elif isinstance(c, UninterpretedFunctionDeclaration):
        var_s, new_env = _alpha_bind(c.name, env, counter)
        type_s = _alpha_type(c.type, new_env, counter)
        seq_s = _alpha_constraint(c.seq, new_env, counter)
        return f"fun {var_s}:{type_s} => {seq_s}"
    elif isinstance(c, ReflectedFunctionDeclaration):
        var_s, new_env = _alpha_bind(c.name, env, counter)
        params_strs = []
        for p in c.params:
            p_s, new_env = _alpha_bind(p, new_env, counter)
            params_strs.append(p_s)
        type_s = _alpha_type(c.type, new_env, counter)
        body_s = _alpha_liquid(c.body, new_env, counter)
        seq_s = _alpha_constraint(c.seq, new_env, counter)
        params_joined = ", ".join(params_strs)
        return f"reflected {var_s}({params_joined}):{type_s} = {body_s} => {seq_s}"
    elif isinstance(c, TypeVarDeclaration):
        var_s, new_env = _alpha_bind(c.name, env, counter)
        seq_s = _alpha_constraint(c.seq, new_env, counter)
        return f"type {var_s}, {seq_s}"
    else:
        return repr(c)


def variables_in_liq(t: LiquidTerm) -> Generator[str, None, None]:
    if isinstance(t, LiquidLiteralBool) or isinstance(t, LiquidLiteralInt) or isinstance(t, LiquidLiteralString):
        pass
    elif isinstance(t, LiquidVar):
        yield str(t.name)
    elif isinstance(t, LiquidApp):
        yield str(t.fun)
        for a in t.args:
            yield from variables_in_liq(a)


def variables_free_in(c: Constraint) -> Generator[str, None, None]:
    if isinstance(c, Conjunction):
        yield from variables_free_in(c.c1)
        yield from variables_free_in(c.c2)
    elif isinstance(c, Implication):
        for k in variables_in_liq(c.pred):
            if k != c.name:
                yield k
        for k in variables_free_in(c.seq):
            if k != c.name:
                yield k
    elif isinstance(c, LiquidConstraint):
        yield from variables_in_liq(c.expr)
    elif isinstance(c, ReflectedFunctionDeclaration):
        yield from variables_in_liq(c.body)
        yield from variables_free_in(c.seq)
