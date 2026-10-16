"""CPSatHole: exact/fixed-point joint optimisation of numeric holes with OR-Tools.

The discrete counterpart of continuous float-hole optimisers. OR-Tools' CP-SAT solver is white-box —
it needs the objective and constraints as a model — so for a program whose holes
are all numeric this synthesizer translates the objective and the holes'
refinements into a CP-SAT model and solves it.

Supported hole types:
  * ``Bool``          -> a CP-SAT Boolean variable;
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
(integer/float ``+``, ``-``, ``*``, literals, comparisons, Boolean ``&&``/``||``,
numeric conditionals, ``Array.get`` with a literal index, ``Array.size``, and
inlined definitions and structurally recursive algebraic data types). Bool holes
and hard @require predicates are supported.
Anything outside this
fragment raises :class:`UnsupportedSynthesisGoal` pointing at another synthesizer backend.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import ceil, floor
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
    Abstraction,
    Application,
    Hole,
    If,
    Let,
    Literal,
    Rec,
    RefinementApplication,
    Term,
    TypeApplication,
    TypeAbstraction,
    Var,
)
from aeon.core.types import RefinedType, Type, TypeConstructor, t_bool, t_float, t_int, top
from aeon.decorators.api import Metadata
from aeon.synthesis.api import ProgramSynthesizer, UnsupportedSynthesisGoal
from aeon.synthesis.decorators import Goal
from aeon.synthesis.identification import get_holes_info, iterate_top_level, term_has_holes
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


@dataclass
class _Bool:
    expr: Any
    known: bool | None = None


@dataclass
class _Data:
    tag: str
    fields: tuple[_Value, ...]


@dataclass
class _Closure:
    binder: Name
    body: Term
    environment: dict[Name, _Value]


@dataclass
class _Constructor:
    tag: str
    arity: int
    arguments: tuple[_Value, ...] = ()


@dataclass
class _Recursor:
    tags: tuple[str, ...]
    arguments: tuple[_Value, ...] = ()


_Value = Union[_Num, _Vec, _Bool, _Data, _Closure, _Constructor, _Recursor]


def _base(ty: object) -> object:
    return ty.type if isinstance(ty, RefinedType) else ty


def _is_int(ty: object) -> bool:
    b = _base(ty)
    return isinstance(b, TypeConstructor) and b.name.name == "Int"


def _is_float(ty: object) -> bool:
    b = _base(ty)
    return isinstance(b, TypeConstructor) and b.name.name == "Float"


def _is_bool(ty: object) -> bool:
    b = _base(ty)
    return isinstance(b, TypeConstructor) and b.name.name == "Bool"


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

    supports_hard_constraints = True

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
            raise UnsupportedSynthesisGoal("CPSatHole requires at least one hole.")

        self._model = cp_model.CpModel()
        self._hole_value: dict[Name, _Value] = {}
        # hole -> (kind, [cp vars]) for decoding the solution.
        self._hole_meta: dict[Name, tuple[str, list[Any]]] = {}
        for hole in all_holes:
            try:
                self._declare_hole(hole, holes_info[hole][0])
            except _Unsupported as e:
                raise UnsupportedSynthesisGoal(
                    f"CPSatHole cannot handle hole {hole.pretty()} ({e}). "
                    "Use a grammar-based synthesizer (e.g. -s gp) instead."
                ) from e

        self._def_bodies = {rec.var_name: rec.var_value for rec in iterate_top_level(term)}
        self._ectx = ectx
        self._term = term
        self._translation_steps = 0
        self._definition_cache: dict[Name, _Value] = {}
        self._application_cache: dict[tuple, tuple[_Closure, _Value, _Value]] = {}
        self._constructor_heads, self._recursor_heads = self._inductive_heads(term)

        goals: list[Goal] = [g for d in metadata.values() for g in d.get("goals", [])]
        if not goals:
            raise UnsupportedSynthesisGoal("CPSatHole requires at least one @minimize/@maximize objective.")

        # Scalarise to a single minimisation objective: orient each goal to
        # minimisation (negate maximise) and align scales before summing.
        oriented: list[_Num] = []
        for goal in goals:
            body = self._def_bodies.get(goal.function)
            if body is None:
                raise UnsupportedSynthesisGoal(f"CPSatHole could not find objective function {goal.function.pretty()}.")
            try:
                value = self._translate(body, {}, frozenset())
            except _Unsupported as e:
                raise UnsupportedSynthesisGoal(
                    f"CPSatHole cannot translate the objective ({e}). Use a grammar-based synthesizer (e.g. -s gp)."
                ) from e
            if not isinstance(value, _Num):
                raise UnsupportedSynthesisGoal("CPSatHole objective must be a number, not an array.")
            if goal.kind == "constraint":
                self._model.add(value.expr == 0)
                continue
            oriented.append(value if goal.minimize else _Num(-value.expr, value.scale, -value.hi, -value.lo))

        target_scale = max((n.scale for n in oriented), default=0)
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
            lo, hi = self._explicit_bounds(ty, 0)
            var = model.new_int_var(lo, hi, f"h_{hole.pretty()}")
            num = _Num(var, 0, lo, hi)
            self._hole_value[hole] = num
            self._hole_meta[hole] = ("int", [var])
            self._apply_scalar_refinement(ty, num)
        elif _is_float(ty):
            lo, hi = self._explicit_bounds(ty, 1)
            var = model.new_int_var(lo, hi, f"h_{hole.pretty()}")
            num = _Num(var, 1, lo, hi)
            self._hole_value[hole] = num
            self._hole_meta[hole] = ("float", [var])
            self._apply_scalar_refinement(ty, num)
        elif _is_bool(ty):
            variable = model.new_bool_var(f"h_{hole.pretty()}")
            self._hole_value[hole] = _Bool(variable)
            self._hole_meta[hole] = ("bool", [variable])
            if isinstance(ty, RefinedType):
                self._boolean_refinement(ty.name, variable, ty.refinement)
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
        if kind == "bool":
            return Literal(bool(solver.value(vars_[0])), type=t_bool)
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
        self._translation_steps += 1
        if self._translation_steps > 100_000:
            raise _Unsupported("structural expansion limit (possibly symbolic recursion)")
        if isinstance(t, Annotation):
            return self._translate(t.expr, env, visited)

        if isinstance(t, (TypeApplication, TypeAbstraction, RefinementApplication)):
            return self._translate(t.body, env, visited)

        if isinstance(t, Abstraction):
            return _Closure(t.var_name, t.body, dict(env))

        if isinstance(t, Hole):
            if t.name in self._hole_value:
                return self._hole_value[t.name]
            raise _Unsupported(f"hole '{t.name.pretty()}'")

        if isinstance(t, (Let, Rec)):
            value = self._translate(t.var_value, env, visited)
            return self._translate(t.body, {**env, t.var_name: value}, visited)

        if isinstance(t, Application) and _head_name(t.fun) == "!":
            value = self._boolean(self._translate(t.arg, env, visited), "!")
            return _Bool(value.expr.Not(), None if value.known is None else not value.known)

        if isinstance(t, If):
            condition = self._boolean(self._translate(t.cond, env, visited), "if")
            if condition.known is not None:
                return self._translate(t.then if condition.known else t.otherwise, env, visited)
            yes_value = self._translate(t.then, env, visited)
            no_value = self._translate(t.otherwise, env, visited)
            if isinstance(yes_value, _Bool) and isinstance(no_value, _Bool):
                boolean = self._model.new_bool_var("if_bool")
                self._model.add(boolean == yes_value.expr).only_enforce_if(condition.expr)
                self._model.add(boolean == no_value.expr).only_enforce_if(condition.expr.Not())
                return _Bool(boolean)
            yes = self._num(yes_value, "if")
            no = self._num(no_value, "if")
            scale = max(yes.scale, no.scale)
            yes, no = self._lift(yes, scale), self._lift(no, scale)
            lo, hi = min(yes.lo, no.lo), max(yes.hi, no.hi)
            result = self._model.new_int_var(lo, hi, "if_result")
            self._model.add(result == yes.expr).only_enforce_if(condition.expr)
            self._model.add(result == no.expr).only_enforce_if(condition.expr.Not())
            return _Num(result, scale, lo, hi)

        # Array.size v  (unary application headed by Array_size).
        if isinstance(t, Application) and _head_name(t.fun) == "Array_size":
            arr = self._translate(t.arg, env, visited)
            if not isinstance(arr, _Vec):
                raise _Unsupported("Array.size of a non-array")
            return _Num(len(arr.items), 0, len(arr.items), len(arr.items))

        binop = _as_binop(t)
        if binop is not None:
            assert isinstance(t, Application)
            op, a, b = binop
            if op == "Array_get":
                arr = self._translate(a, env, visited)
                idx = self._translate(b, env, visited)
                if not isinstance(arr, _Vec) or not isinstance(idx, _Num) or not isinstance(idx.expr, int):
                    raise _Unsupported("Array.get needs an array and a constant index")
                if not (0 <= idx.expr < len(arr.items)):
                    raise _Unsupported(f"Array.get index {idx.expr} out of range")
                return arr.items[idx.expr]
            if op in ("&&", "||"):
                av = self._boolean(self._translate(a, env, visited), op)
                bv = self._boolean(self._translate(b, env, visited), op)
                a_bool, b_bool = av.expr, bv.expr
                result_bool = self._model.new_bool_var("logical")
                if op == "&&":
                    self._model.add_bool_and([a_bool, b_bool]).only_enforce_if(result_bool)
                    self._model.add_bool_or([a_bool.Not(), b_bool.Not()]).only_enforce_if(result_bool.Not())
                else:
                    self._model.add_bool_or([a_bool, b_bool]).only_enforce_if(result_bool)
                    self._model.add_bool_and([a_bool.Not(), b_bool.Not()]).only_enforce_if(result_bool.Not())
                known = None
                if av.known is not None and bv.known is not None:
                    known = (av.known and bv.known) if op == "&&" else (av.known or bv.known)
                return _Bool(result_bool, known)
            if op not in ("+", "-", "*", "%", "<", "<=", ">", ">=", "==", "!="):
                return self._apply(self._translate(t.fun, env, visited), self._translate(t.arg, env, visited), visited)
            a_value = self._translate(a, env, visited)
            b_value = self._translate(b, env, visited)
            if op in ("==", "!=") and isinstance(a_value, _Bool) and isinstance(b_value, _Bool):
                comparison = self._model.new_bool_var("bool_comparison")
                inverse = "!=" if op == "==" else "=="
                self._model.add(self._compare(op, a_value.expr, b_value.expr)).only_enforce_if(comparison)
                self._model.add(self._compare(inverse, a_value.expr, b_value.expr)).only_enforce_if(comparison.Not())
                known = None
                if a_value.known is not None and b_value.known is not None:
                    known = (a_value.known == b_value.known) if op == "==" else (a_value.known != b_value.known)
                return _Bool(comparison, known)
            ea = self._num(a_value, op)
            eb = self._num(b_value, op)
            if op in ("<", "<=", ">", ">=", "==", "!="):
                scale = max(ea.scale, eb.scale)
                left, right = self._lift(ea, scale).expr, self._lift(eb, scale).expr
                comparison = self._model.new_bool_var("comparison")
                inverse = {"<": ">=", "<=": ">", ">": "<=", ">=": "<", "==": "!=", "!=": "=="}[op]
                self._model.add(self._compare(op, left, right)).only_enforce_if(comparison)
                self._model.add(self._compare(inverse, left, right)).only_enforce_if(comparison.Not())
                known = None
                if isinstance(left, int) and isinstance(right, int):
                    known = bool(self._compare(op, left, right))
                return _Bool(comparison, known)
            return self._arith(op, ea, eb)

        if isinstance(t, Literal):
            if isinstance(t.value, bool):
                return _Bool(self._model.new_constant(int(t.value)), t.value)
            if isinstance(t.value, int):
                return _Num(t.value, 0, t.value, t.value)
            if isinstance(t.value, float):
                return self._literal_number(t.value)
            raise _Unsupported("non-numeric literal")

        if isinstance(t, Var):
            if t.name in env:
                return env[t.name]
            if t.name in self._constructor_heads:
                return self._constructor_heads[t.name]
            if t.name in self._recursor_heads:
                return _Recursor(self._recursor_heads[t.name])
            if t.name in self._definition_cache:
                return self._definition_cache[t.name]
            if t.name in self._def_bodies:
                body = self._def_bodies[t.name]
                while isinstance(body, TypeAbstraction):
                    body = body.body
                if isinstance(body, Abstraction):
                    value = self._translate(body, {}, visited)
                    self._definition_cache[t.name] = value
                    return value
            if t.name in self._def_bodies and t.name not in visited:
                try:
                    value = self._translate(self._def_bodies[t.name], {}, visited | {t.name})
                    self._definition_cache[t.name] = value
                    return value
                except _Unsupported:
                    pass
            return self._eval_const(t.name)

        if isinstance(t, Application):
            return self._apply(self._translate(t.fun, env, visited), self._translate(t.arg, env, visited), visited)

        raise _Unsupported(type(t).__name__)

    def _apply(self, function: _Value, argument: _Value, visited: frozenset[Name]) -> _Value:
        if isinstance(function, _Closure):
            body = function.body
            if (
                isinstance(body, Application)
                and _head_name(body.fun) == "native"
                and isinstance(body.arg, Literal)
                and body.arg.value == f"float({function.binder.name})"
            ):
                # Exact numerical interpretation of the scalar cast. This
                # recognizes one expression, never evaluates native code.
                return self._num(argument, "float conversion")
            key = (
                id(function.body),
                tuple(
                    (name.id, name.name, self._value_key(value)) for name, value in sorted(function.environment.items())
                ),
                self._value_key(argument),
            )
            if key in self._application_cache:
                return self._application_cache[key][2]
            result = self._translate(function.body, {**function.environment, function.binder: argument}, visited)
            # Retain inputs alongside the result: identity keys must never
            # alias later objects after Python recycles an object identifier.
            self._application_cache[key] = (function, argument, result)
            return result
        if isinstance(function, _Constructor):
            arguments = (*function.arguments, argument)
            if len(arguments) == function.arity:
                return _Data(function.tag, arguments)
            return _Constructor(function.tag, function.arity, arguments)
        if isinstance(function, _Recursor):
            arguments = (*function.arguments, argument)
            if len(arguments) < len(function.tags) + 1:
                return _Recursor(function.tags, arguments)
            data = arguments[0]
            if not isinstance(data, _Data) or data.tag not in function.tags:
                raise _Unsupported("match on a value without a known constructor")
            branch = arguments[1 + function.tags.index(data.tag)]
            for field in data.fields:
                branch = self._apply(branch, field, visited)
            return branch
        raise _Unsupported("application of a non-function")

    @staticmethod
    def _value_key(value: _Value) -> tuple:
        if isinstance(value, _Num):
            expression = ("constant", value.expr) if isinstance(value.expr, int) else ("symbolic", id(value.expr))
            return ("number", expression, value.scale)
        if isinstance(value, _Bool) and value.known is not None:
            return ("boolean", value.known)
        return (type(value).__name__, id(value))

    @staticmethod
    def _inductive_heads(term: Term) -> tuple[dict[Name, _Value], dict[Name, tuple[str, ...]]]:
        """Recognize the compiler's exact constructor and recursor encodings.

        Pattern matching is unfolded on concrete ADT spines while fields may
        contain numeric holes. No native string is executed by this adapter.
        """
        import re
        from aeon.verification.constructor_registry import get_constructor_groups, get_constructor_order

        groups = get_constructor_groups()
        all_tags = {tag for tags in groups.values() for tag in tags}
        constructors: dict[Name, _Value] = {}
        recursors: dict[Name, tuple[str, ...]] = {}
        for binding in iterate_top_level(term):
            body = binding.var_value
            arguments: list[str] = []
            while isinstance(body, (TypeAbstraction, Abstraction)):
                if isinstance(body, Abstraction):
                    arguments.append(body.var_name.name)
                body = body.body
            if (
                not isinstance(body, Application)
                or _head_name(body.fun) != "native"
                or not isinstance(body.arg, Literal)
            ):
                continue
            code = body.arg.value
            if not isinstance(code, str):
                continue
            matched = re.fullmatch(r"\('([^']+)', (.*)\)", code)
            if matched and matched[1] in all_tags and matched[2] == ", ".join(arguments):
                tag = matched[1]
                constructors[binding.var_name] = _Constructor(tag, len(arguments)) if arguments else _Data(tag, ())
            for type_name in groups:
                tags = tuple(get_constructor_order(type_name) or [])
                if binding.var_name.name != type_name + "_rec" or len(arguments) != len(tags) + 1:
                    continue
                expected = "(_ for _ in ()).throw(Exception('Invalid constructor'))"
                for tag in reversed(tags):
                    from aeon.verification.constructor_registry import get_constructor_fields

                    fields = get_constructor_fields(tag) or []
                    case = "case_" + tag[len(type_name) + 1 :]
                    branch = case + "".join(f"(this[{i + 1}])" for i in range(len(fields)))
                    expected = f"({branch} if this[0] == '{tag}' else {expected})"
                if code == expected:
                    recursors[binding.var_name] = tags
        return constructors, recursors

    @staticmethod
    def _num(v: _Value, op: str) -> _Num:
        if isinstance(v, _Num):
            return v
        raise _Unsupported(f"non-numeric operand to '{op}'")

    @staticmethod
    def _boolean(v: _Value, op: str) -> _Bool:
        if isinstance(v, _Bool):
            return v
        raise _Unsupported(f"non-boolean operand to '{op}'")

    def _arith(self, op: str, a: _Num, b: _Num) -> _Num:
        if op == "%":
            if a.scale == b.scale == 0 and isinstance(a.expr, int) and isinstance(b.expr, int) and b.expr:
                value = a.expr % b.expr
                return _Num(value, 0, value, value)
            raise _Unsupported("remainder requires constant integer operands")
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
        from dataclasses import replace

        bindings = []
        for binding in iterate_top_level(self._term):
            if term_has_holes(binding.var_value):
                # Never enter the interpreter's interactive Hole handler while
                # trying to recover from an unsupported symbolic expression.
                raise _Unsupported(f"constant '{name.pretty()}' occurs after unresolved holes")
            bindings.append(binding)
            if binding.var_name == name:
                break
        else:
            bindings = []
        expression: Term = Var(name)
        for binding in reversed(bindings):
            expression = replace(binding, body=expression)
        try:
            value = aeon_eval(expression, self._ectx)
        except Exception as e:  # noqa: BLE001
            raise _Unsupported(f"variable '{name.pretty()}'") from e
        if isinstance(value, bool):
            raise _Unsupported(f"boolean variable '{name.pretty()}'")
        if isinstance(value, int):
            return _Num(value, 0, value, value)
        if isinstance(value, float):
            return self._literal_number(value)
        raise _Unsupported(f"non-numeric variable '{name.pretty()}'")

    # -- refinement translation ------------------------------------------

    def _boolean_refinement(self, binder: Name, variable: Any, predicate: LiquidTerm) -> None:
        def expression(term: LiquidTerm) -> Any:
            if isinstance(term, LiquidLiteralBool):
                return self._model.new_constant(int(term.value))
            if isinstance(term, LiquidVar) and term.name == binder:
                return variable
            if isinstance(term, LiquidApp) and term.fun.name == "!" and len(term.args) == 1:
                return expression(term.args[0]).Not()
            if isinstance(term, LiquidApp) and term.fun.name in ("==", "!="):
                left, right = map(expression, term.args)
                result = self._model.new_bool_var("bool_refinement")
                op = term.fun.name
                self._model.add(self._compare(op, left, right)).only_enforce_if(result)
                self._model.add(self._compare("!=" if op == "==" else "==", left, right)).only_enforce_if(result.Not())
                return result
            raise _Unsupported("Boolean refinement predicate")

        if isinstance(predicate, LiquidApp) and predicate.fun.name == "&&":
            for child in predicate.args:
                self._boolean_refinement(binder, variable, child)
            return
        self._model.add_bool_or([expression(predicate)])

    def _explicit_bounds(self, ty: Type, scale: int) -> tuple[int, int]:
        """Use declared constant bounds; the configured bound is a fallback.

        A model explicitly declaring 0 <= x <= 10000 must not silently search
        only 0..1000. Precise bounds also avoid excessive product intervals.
        """
        lower: int | None = None
        upper: int | None = None
        fallback = self.bound * self.scale**scale
        if not isinstance(ty, RefinedType):
            return -fallback, fallback

        def mentions_variable(expression: LiquidTerm) -> bool:
            if isinstance(expression, LiquidVar):
                return True
            return isinstance(expression, LiquidApp) and any(mentions_variable(arg) for arg in expression.args)

        def visit(predicate: LiquidTerm) -> None:
            nonlocal lower, upper
            if not isinstance(predicate, LiquidApp):
                return
            op = predicate.fun.name
            if op == "&&":
                for child in predicate.args:
                    visit(child)
                return
            if op not in ("<", "<=", ">", ">=", "==") or len(predicate.args) != 2:
                return
            left, right = predicate.args
            if isinstance(right, LiquidVar) and right.name == ty.name:
                left, right = right, left
                op = {"<": ">", "<=": ">=", ">": "<", ">=": "<=", "==": "=="}[op]
            if not isinstance(left, LiquidVar) or left.name != ty.name:
                return
            if mentions_variable(right):
                return
            try:
                constant = self._liquid(ty.name, _Num(0, scale, 0, 0), right)
            except _Unsupported:
                return
            if not isinstance(constant.expr, int):
                return
            value = Fraction(constant.expr) * Fraction(self.scale) ** (scale - constant.scale)
            if op in (">", ">=", "=="):
                candidate = floor(value) + 1 if op == ">" else ceil(value)
                lower = candidate if lower is None else max(lower, candidate)
            if op in ("<", "<=", "=="):
                candidate = ceil(value) - 1 if op == "<" else floor(value)
                upper = candidate if upper is None else min(upper, candidate)

        visit(ty.refinement)
        lo, hi = lower if lower is not None else -fallback, upper if upper is not None else fallback
        if lo > hi:
            self._model.add_bool_or([])
            return 0, 0
        return lo, hi

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

    def _literal_number(self, value: float) -> _Num:
        """Preserve decimal constants exactly; only holes use the search grid."""
        fraction = Fraction(str(value))
        for level in range(7):
            scaled = fraction * self.scale**level
            if scaled.denominator == 1:
                integer = scaled.numerator
                return _Num(integer, level, integer, integer)
        raise _Unsupported(f"decimal constant {value} exceeds supported precision")

    def _liquid(self, binder: Name, hole: _Num, lt: LiquidTerm) -> _Num:
        if isinstance(lt, LiquidVar):
            if lt.name == binder:
                return hole
            raise _Unsupported(f"variable '{lt.name.pretty()}'")
        if isinstance(lt, LiquidLiteralInt):
            return _Num(lt.value, 0, lt.value, lt.value)
        if isinstance(lt, LiquidLiteralFloat):
            return self._literal_number(lt.value)
        if isinstance(lt, LiquidApp) and lt.fun.name in ("+", "-", "*"):
            return self._arith(
                lt.fun.name, self._liquid(binder, hole, lt.args[0]), self._liquid(binder, hole, lt.args[1])
            )
        raise _Unsupported(f"term '{getattr(getattr(lt, 'fun', None), 'name', type(lt).__name__)}'")


# Backwards-compatible alias (the backend now handles Float and arrays too).
IntHoleCPSynthesizer = CPSatHoleSynthesizer
