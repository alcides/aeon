from __future__ import annotations

from dataclasses import dataclass
from contextlib import contextmanager, ExitStack
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


def conjoin(c1: Constraint, c2: Constraint) -> Constraint:
    """Drop literal-true identities as verification conditions are built."""
    if isinstance(c1, LiquidConstraint) and isinstance(c1.expr, LiquidLiteralBool) and c1.expr.value:
        return c2
    if isinstance(c2, LiquidConstraint) and isinstance(c2.expr, LiquidLiteralBool) and c2.expr.value:
        return c1
    return Conjunction(c1, c2)


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


@contextmanager
def _alpha_scope(name: Name, env: dict[tuple[str, int], int], counter: list[int]):
    """Temporarily extend a scope without copying the full enclosing map."""
    key = (name.name, name.id)
    previous = env.get(key)
    canonical_id = counter[0]
    counter[0] += 1
    env[key] = canonical_id
    try:
        yield f"{name.name}#{canonical_id}"
    finally:
        if previous is None:
            del env[key]
        else:
            env[key] = previous


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
        with _alpha_scope(ty.var_name, env, counter) as var_s:
            vt_s = _alpha_type(ty.var_type, env, counter)
            body_s = _alpha_type(ty.type, env, counter)
            return f"({var_s}:{vt_s}) -> {body_s}"
    elif isinstance(ty, RefinedType):
        with _alpha_scope(ty.name, env, counter) as var_s:
            base_s = _alpha_type(ty.type, env, counter)
            ref_s = _alpha_liquid(ty.refinement, env, counter)
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
        with _alpha_scope(ty.name, env, counter) as var_s:
            body_s = _alpha_type(ty.body, env, counter)
            return f"forall {var_s}:{ty.kind}, {body_s}"
    elif isinstance(ty, RefinementPolymorphism):
        with _alpha_scope(ty.name, env, counter) as var_s:
            sort_s = _alpha_type(ty.sort, env, counter)
            body_s = _alpha_type(ty.body, env, counter)
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
    return "".join(_alpha_constraint_parts(c, env, counter))


def _alpha_constraint_parts(
    c: Constraint, env: dict[tuple[str, int], int], counter: list[int]
) -> Generator[str, None, None]:
    """Stream canonical constraints with an explicit, scope-preserving stack."""
    pending: list[Constraint | str | ExitStack] = [c]
    scopes: list[ExitStack] = []
    try:
        while pending:
            item = pending.pop()
            if isinstance(item, str):
                yield item
            elif isinstance(item, ExitStack):
                scopes.pop().close()
            elif isinstance(item, LiquidConstraint):
                yield _alpha_liquid(item.expr, env, counter)
            elif isinstance(item, Conjunction):
                pending.extend((")", item.c2, ") ∧ (", item.c1, "("))
            elif isinstance(
                item, (Implication, UninterpretedFunctionDeclaration, ReflectedFunctionDeclaration, TypeVarDeclaration)
            ):
                scope = ExitStack()
                scopes.append(scope)
                var_s = scope.enter_context(_alpha_scope(item.name, env, counter))
                if isinstance(item, Implication):
                    prefix = f"∀{var_s}:{_alpha_type(item.base, env, counter)}, ({_alpha_liquid(item.pred, env, counter)}) => "
                elif isinstance(item, UninterpretedFunctionDeclaration):
                    prefix = f"fun {var_s}:{_alpha_type(item.type, env, counter)} => "
                elif isinstance(item, ReflectedFunctionDeclaration):
                    params = [scope.enter_context(_alpha_scope(p, env, counter)) for p in item.params]
                    prefix = (
                        f"reflected {var_s}({', '.join(params)}):{_alpha_type(item.type, env, counter)}"
                        f" = {_alpha_liquid(item.body, env, counter)} => "
                    )
                else:
                    prefix = f"type {var_s}, "
                pending.extend((scope, item.seq, prefix))
            else:
                yield repr(item)
    finally:
        while scopes:
            scopes.pop().close()


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
