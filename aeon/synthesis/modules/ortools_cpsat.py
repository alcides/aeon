"""CPSatHole: exact/fixed-point joint optimisation of numeric holes with OR-Tools.

The discrete counterpart of FloatHoleNG. OR-Tools' CP-SAT solver is white-box —
it needs the objective and constraints as a model — so for a program whose holes
are all numeric this synthesizer translates the objective and the holes'
refinements into a CP-SAT model and solves it.

Supported hole types:
  * ``Int``           -> a CP-SAT integer variable (exact);
  * ``Float``         -> a fixed-point integer variable (value ``= var / SCALE``);
  * ``(Array Int)``   -> one integer variable per element (exact);
  * ``(Array Float)`` -> one fixed-point variable per element.

CP-SAT has no continuous variables, so Float holes are modelled in fixed point:
each float is an integer multiple of ``1 / SCALE`` (default 1/1000). Results are
therefore exact for Int and snapped to that grid for Float. Each translated
value carries a *scale* (the power of ``SCALE`` baked into its integer
expression); ``+``/``-`` align scales and ``*`` adds them.

The objective is the ``@minimize``/``@maximize`` expression over the holes
(integer/float ``+``, ``-``, ``*``, literals, ``Array.get`` with a literal
index, ``Array.size``, and inlined closed definitions). Anything outside this
fragment raises :class:`SynthesisError` pointing at a grammar/Nevergrad backend.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Optional, Union

from aeon.backend.evaluator import EvaluationContext
from aeon.backend.evaluator import eval as aeon_eval
from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralFloat,
    LiquidLiteralInt,
    LiquidTerm,
    LiquidVar,
)
from aeon.core.terms import (
    Annotation,
    Application,
    Hole,
    Let,
    Literal,
    Rec,
    RefinementApplication,
    Term,
    TypeApplication,
    Var,
)
from aeon.core.types import RefinedType, Type, TypeConstructor, t_float, t_int, top
from aeon.decorators.api import Metadata
from aeon.synthesis.api import ProgramSynthesizer, SynthesisError
from aeon.synthesis.decorators import Goal
from aeon.synthesis.evaluation_pool import set_program_tail
from aeon.synthesis.identification import get_holes_info, iterate_top_level
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

DEFAULT_BOUND = 1000
# Fixed-point resolution for Float holes: a float is represented as an integer
# multiple of 1 / SCALE.
DEFAULT_SCALE = 1000


class _Unsupported(Exception):
    """A term/refinement construct outside the CP-SAT-translatable fragment."""


@dataclass
class _Num:
    """A scalar value: real value ``= expr / SCALE**scale`` (expr is an int or a
    CP-SAT linear expression). ``lo``/``hi`` bound ``expr``."""

    expr: Any
    scale: int
    lo: int
    hi: int


@dataclass
class _Vec:
    """An array value: one ``_Num`` per element."""

    items: list[_Num]


_Value = Union[_Num, _Vec]


def _base(ty: object) -> object:
    return ty.type if isinstance(ty, RefinedType) else ty


def _is_int(ty: object) -> bool:
    b = _base(ty)
    return isinstance(b, TypeConstructor) and b.name.name == "Int"


def _is_float(ty: object) -> bool:
    b = _base(ty)
    return isinstance(b, TypeConstructor) and b.name.name == "Float"


def _array_elem(ty: object) -> str | None:
    """``'int'``/``'float'`` for an ``(Array Int)``/``(Array Float)`` type, else None."""
    b = _base(ty)
    if isinstance(b, TypeConstructor) and b.name.name == "Array" and len(b.args) == 1:
        if _is_int(b.args[0]):
            return "int"
        if _is_float(b.args[0]):
            return "float"
    return None


def _head_name(t: Term) -> str | None:
    """Variable name at the head of an application, peeling type/refinement
    applications and annotations."""
    while isinstance(t, (TypeApplication, RefinementApplication, Annotation)):
        t = t.expr if isinstance(t, Annotation) else t.body
    return t.name.name if isinstance(t, Var) else None


def _as_binop(t: Term) -> tuple[str, Term, Term] | None:
    if isinstance(t, Application) and isinstance(t.fun, Application):
        op = _head_name(t.fun.fun)
        if op is not None:
            return op, t.fun.arg, t.arg
    return None


def _array_length(ty: Type) -> int | None:
    """Extract ``k`` from an array hole refined by ``Array_size a == k``."""
    if not isinstance(ty, RefinedType):
        return None
    found: list[int] = []

    def walk(lt: LiquidTerm) -> None:
        if isinstance(lt, LiquidApp):
            name = getattr(lt.fun, "name", str(lt.fun))
            if name == "==" and len(lt.args) == 2:
                a, b = lt.args
                for x, y in ((a, b), (b, a)):
                    if isinstance(x, LiquidApp) and "size" in getattr(x.fun, "name", "").lower():
                        if isinstance(y, LiquidLiteralInt):
                            found.append(y.value)
            for a in lt.args:
                walk(a)

    walk(ty.refinement)
    return found[0] if found else None


class CPSatHoleSynthesizer(ProgramSynthesizer):
    """Exact/fixed-point joint numeric-hole optimisation via OR-Tools CP-SAT.

    Args:
        bound: each unconstrained scalar hole is searched in ``[-bound, bound]``
            (in real units; Float vars use ``[-bound*scale, bound*scale]``).
        scale: fixed-point resolution for Float holes (a float is an integer
            multiple of ``1/scale``).
        seed: CP-SAT random seed (kept for API parity; the search is exact).
    """

    def __init__(self, bound: int = DEFAULT_BOUND, scale: int = DEFAULT_SCALE, seed: int = 0):
        self.bound = bound
        self.scale = scale
        self.seed = seed

    def synthesize_program(
        self,
        ctx: TypingContext,
        ectx: EvaluationContext,
        term: Term,
        targets: list[tuple[Name, list[Name]]],
        metadata: Metadata,
        budget: float = 60,
        ui: SynthesisUI = SynthesisUI(),
    ) -> dict[Name, Optional[Term]]:
        try:
            from ortools.sat.python import cp_model
        except ImportError as e:  # pragma: no cover - optional dependency
            raise ImportError(
                "CPSatHole requires the 'ortools' package. Install it with "
                "`uv pip install ortools` (or the 'synthesis-ortools' extra)."
            ) from e

        all_holes = [h for _, hs in targets for h in hs]
        holes_info = get_holes_info(ctx, term, top, targets, refined_types=True)
        if not all_holes:
            raise SynthesisError("CPSatHole requires at least one hole.")

        self._model = cp_model.CpModel()
        self._hole_value: dict[Name, _Value] = {}
        # hole -> (kind, [cp vars]) for decoding the solution.
        self._hole_meta: dict[Name, tuple[str, list[Any]]] = {}
        for hole in all_holes:
            try:
                self._declare_hole(hole, holes_info[hole][0])
            except _Unsupported as e:
                raise SynthesisError(
                    f"CPSatHole cannot handle hole {hole.pretty()} ({e}). "
                    "Use a grammar-based synthesizer (e.g. -s ng / gp) instead."
                ) from e

        self._def_bodies = {rec.var_name: rec.var_value for rec in iterate_top_level(term)}
        self._ectx = ectx
        self._term = term

        goals: list[Goal] = [g for d in metadata.values() for g in d.get("goals", [])]
        if not goals:
            raise SynthesisError("CPSatHole requires at least one @minimize/@maximize objective.")

        # Scalarise to a single minimisation objective: orient each goal to
        # minimisation (negate maximise) and align scales before summing.
        oriented: list[_Num] = []
        for goal in goals:
            body = self._def_bodies.get(goal.function)
            if body is None:
                raise SynthesisError(f"CPSatHole could not find objective function {goal.function.pretty()}.")
            try:
                value = self._translate(body, {}, frozenset())
            except _Unsupported as e:
                raise SynthesisError(
                    f"CPSatHole cannot translate the objective ({e}). "
                    "Use a grammar-based synthesizer (e.g. -s ng / gp)."
                ) from e
            if not isinstance(value, _Num):
                raise SynthesisError("CPSatHole objective must be a number, not an array.")
            oriented.append(value if goal.minimize else _Num(-value.expr, value.scale, -value.hi, -value.lo))

        target_scale = max(n.scale for n in oriented)
        model = self._model
        model.minimize(sum(self._lift(n, target_scale).expr for n in oriented))

        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = float(budget)
        solver.parameters.random_seed = self.seed
        ui.start(ctx, ectx, "+".join(h.name for h in all_holes), top, budget)
        status = solver.solve(model)

        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            ui.end(None, None)
            return {hole: None for hole in all_holes}

        mapping: dict[Name, Optional[Term]] = {h: self._decode(solver, h) for h in all_holes}
        ui.end(None, None)
        return mapping

    # -- hole declaration -------------------------------------------------

    def _declare_hole(self, hole: Name, ty: Type) -> None:
        model = self._model
        if _is_int(ty):
            var = model.new_int_var(-self.bound, self.bound, f"h_{hole.pretty()}")
            num = _Num(var, 0, -self.bound, self.bound)
            self._hole_value[hole] = num
            self._hole_meta[hole] = ("int", [var])
            self._apply_scalar_refinement(ty, num)
        elif _is_float(ty):
            b = self.bound * self.scale
            var = model.new_int_var(-b, b, f"h_{hole.pretty()}")
            num = _Num(var, 1, -b, b)
            self._hole_value[hole] = num
            self._hole_meta[hole] = ("float", [var])
            self._apply_scalar_refinement(ty, num)
        elif (elem := _array_elem(ty)) is not None:
            k = _array_length(ty)
            if k is None or k < 0:
                raise _Unsupported("Array hole without a fixed 'size a == k' refinement")
            scale = 0 if elem == "int" else 1
            b = self.bound if elem == "int" else self.bound * self.scale
            items = []
            vars_ = []
            for i in range(k):
                v = model.new_int_var(-b, b, f"h_{hole.pretty()}_{i}")
                items.append(_Num(v, scale, -b, b))
                vars_.append(v)
            self._hole_value[hole] = _Vec(items)
            self._hole_meta[hole] = (f"array_{elem}", vars_)
        else:
            raise _Unsupported(f"type {_base(ty)}")

    def _decode(self, solver: Any, hole: Name) -> Term:
        kind, vars_ = self._hole_meta[hole]
        if kind == "int":
            return Literal(int(solver.value(vars_[0])), type=t_int)
        if kind == "float":
            return Literal(solver.value(vars_[0]) / self.scale, type=t_float)
        arrty = TypeConstructor(Name("Array", 0), [t_int if kind == "array_int" else t_float])
        if kind == "array_int":
            return Literal([int(solver.value(v)) for v in vars_], type=arrty)
        return Literal([solver.value(v) / self.scale for v in vars_], type=arrty)

    # -- scale helpers ----------------------------------------------------

    def _lift(self, n: _Num, target: int) -> _Num:
        if n.scale == target:
            return n
        f = self.scale ** (target - n.scale)
        return _Num(n.expr * f, target, n.lo * f, n.hi * f)

    # -- objective translation -------------------------------------------

    def _translate(self, t: Term, env: dict[Name, _Value], visited: frozenset[Name]) -> _Value:
        if isinstance(t, Annotation):
            return self._translate(t.expr, env, visited)

        if isinstance(t, Hole):
            if t.name in self._hole_value:
                return self._hole_value[t.name]
            raise _Unsupported(f"hole '{t.name.pretty()}'")

        if isinstance(t, (Let, Rec)):
            value = self._translate(t.var_value, env, visited)
            return self._translate(t.body, {**env, t.var_name: value}, visited)

        # Array.size v  (unary application headed by Array_size).
        if isinstance(t, Application) and _head_name(t.fun) == "Array_size":
            arr = self._translate(t.arg, env, visited)
            if not isinstance(arr, _Vec):
                raise _Unsupported("Array.size of a non-array")
            return _Num(len(arr.items), 0, len(arr.items), len(arr.items))

        binop = _as_binop(t)
        if binop is not None:
            op, a, b = binop
            if op == "Array_get":
                arr = self._translate(a, env, visited)
                idx = self._translate(b, env, visited)
                if not isinstance(arr, _Vec) or not isinstance(idx, _Num) or not isinstance(idx.expr, int):
                    raise _Unsupported("Array.get needs an array and a constant index")
                if not (0 <= idx.expr < len(arr.items)):
                    raise _Unsupported(f"Array.get index {idx.expr} out of range")
                return arr.items[idx.expr]
            ea = self._num(self._translate(a, env, visited), op)
            eb = self._num(self._translate(b, env, visited), op)
            return self._arith(op, ea, eb)

        if isinstance(t, Literal):
            if isinstance(t.value, bool):
                raise _Unsupported("boolean literal")
            if isinstance(t.value, int):
                return _Num(t.value, 0, t.value, t.value)
            if isinstance(t.value, float):
                v = round(t.value * self.scale)
                return _Num(v, 1, v, v)
            raise _Unsupported("non-numeric literal")

        if isinstance(t, Var):
            if t.name in env:
                return env[t.name]
            if t.name in self._def_bodies and t.name not in visited:
                try:
                    return self._translate(self._def_bodies[t.name], {}, visited | {t.name})
                except _Unsupported:
                    pass
            return self._eval_const(t.name)

        raise _Unsupported(type(t).__name__)

    @staticmethod
    def _num(v: _Value, op: str) -> _Num:
        if isinstance(v, _Num):
            return v
        raise _Unsupported(f"array operand to '{op}'")

    def _arith(self, op: str, a: _Num, b: _Num) -> _Num:
        if op in ("+", "-"):
            s = max(a.scale, b.scale)
            a, b = self._lift(a, s), self._lift(b, s)
            if op == "+":
                return _Num(a.expr + b.expr, s, a.lo + b.lo, a.hi + b.hi)
            return _Num(a.expr - b.expr, s, a.lo - b.hi, a.hi - b.lo)
        if op == "*":
            s = a.scale + b.scale
            corners = [a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi]
            lo, hi = min(corners), max(corners)
            if isinstance(a.expr, int) or isinstance(b.expr, int):
                return _Num(a.expr * b.expr, s, lo, hi)
            prod = self._model.new_int_var(lo, hi, "prod")
            self._model.add_multiplication_equality(prod, [a.expr, b.expr])
            return _Num(prod, s, lo, hi)
        raise _Unsupported(f"operator '{op}'")

    def _eval_const(self, name: Name) -> _Num:
        try:
            value = aeon_eval(set_program_tail(self._term, Var(name)), self._ectx)
        except Exception as e:  # noqa: BLE001
            raise _Unsupported(f"variable '{name.pretty()}'") from e
        if isinstance(value, bool):
            raise _Unsupported(f"boolean variable '{name.pretty()}'")
        if isinstance(value, int):
            return _Num(value, 0, value, value)
        if isinstance(value, float):
            v = round(value * self.scale)
            return _Num(v, 1, v, v)
        raise _Unsupported(f"non-numeric variable '{name.pretty()}'")

    # -- refinement translation ------------------------------------------

    def _apply_scalar_refinement(self, ty: Type, hole: _Num) -> None:
        if not isinstance(ty, RefinedType):
            return
        try:
            self._add_refinement(ty.name, hole, ty.refinement)
        except _Unsupported as e:
            raise _Unsupported(f"refinement {e}") from e

    def _add_refinement(self, binder: Name, hole: _Num, pred: LiquidTerm) -> None:
        if isinstance(pred, LiquidLiteralBool):
            if not pred.value:
                self._model.add_bool_or([])
            return
        if isinstance(pred, LiquidApp):
            op = pred.fun.name
            if op == "&&":
                for arg in pred.args:
                    self._add_refinement(binder, hole, arg)
                return
            if op in ("<", "<=", ">", ">=", "==", "!="):
                left = self._liquid(binder, hole, pred.args[0])
                right = self._liquid(binder, hole, pred.args[1])
                s = max(left.scale, right.scale)
                lo, hi = self._lift(left, s).expr, self._lift(right, s).expr
                self._model.add(self._compare(op, lo, hi))
                return
        raise _Unsupported(f"predicate '{getattr(getattr(pred, 'fun', None), 'name', pred)}'")

    @staticmethod
    def _compare(op: str, left: Any, right: Any) -> Any:
        return {
            "<": left < right,
            "<=": left <= right,
            ">": left > right,
            ">=": left >= right,
            "==": left == right,
            "!=": left != right,
        }[op]

    def _liquid(self, binder: Name, hole: _Num, lt: LiquidTerm) -> _Num:
        if isinstance(lt, LiquidVar):
            if lt.name == binder:
                return hole
            raise _Unsupported(f"variable '{lt.name.pretty()}'")
        if isinstance(lt, LiquidLiteralInt):
            return _Num(lt.value, 0, lt.value, lt.value)
        if isinstance(lt, LiquidLiteralFloat):
            v = round(lt.value * self.scale)
            return _Num(v, 1, v, v)
        if isinstance(lt, LiquidApp) and lt.fun.name in ("+", "-", "*"):
            return self._arith(
                lt.fun.name, self._liquid(binder, hole, lt.args[0]), self._liquid(binder, hole, lt.args[1])
            )
        raise _Unsupported(f"term '{getattr(getattr(lt, 'fun', None), 'name', type(lt).__name__)}'")


# Backwards-compatible alias (the backend now handles Float and arrays too).
IntHoleCPSynthesizer = CPSatHoleSynthesizer
