"""Phase 1 of issue #49: convert an Aeon-core synthesis problem to SyGuS.

``build_sygus_problem`` inspects the hole type and its typing context and,
when the problem falls inside the supported subset, produces a
``SygusProblem`` — a solver-agnostic description that the cvc5 solver
(``solver.py``) consumes.  ``problem_to_sl`` renders the same problem into
SyGuS-IF (``.sl``) text, which is handy for logging and debugging.

Anything outside the subset makes ``build_sygus_problem`` return ``None`` so
the caller can report a clean failure (the issue's "graceful failure if
conversion isn't feasible").
"""

from __future__ import annotations

from dataclasses import dataclass

from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralFloat,
    LiquidLiteralInt,
    LiquidLiteralString,
    LiquidTerm,
    LiquidVar,
    liquid_free_vars,
)
from aeon.core.types import RefinedType, Type, TypeConstructor, t_bool, t_float, t_int
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name, fresh_counter

# SyGuS / SMT-LIB sort for each Aeon base type.
_SORT_OF_BASE: dict[TypeConstructor, str] = {t_int: "Int", t_bool: "Bool", t_float: "Real"}

# Aeon native operator -> SMT-LIB symbol (same arity).  ``==``/``!=`` and
# integer division are handled specially in ``liquid_to_smt``.
_OP_TO_SMT: dict[str, str] = {
    "<": "<",
    "<=": "<=",
    ">": ">",
    ">=": ">=",
    "&&": "and",
    "||": "or",
    "!": "not",
    "-->": "=>",
    "+": "+",
    "-": "-",
    "*": "*",
    "%": "mod",
}


def smt_sort_of(ty: Type) -> str | None:
    """Return the SMT-LIB sort for an Aeon base/refined base type, else None."""
    base = ty.type if isinstance(ty, RefinedType) else ty
    if isinstance(base, TypeConstructor):
        return _SORT_OF_BASE.get(base)
    return None


@dataclass
class SygusParam:
    """A context variable lifted into an input of the synthesised function."""

    aeon_name: Name
    aeon_type: Type
    smt_name: str
    sort: str


@dataclass
class SygusProblem:
    """A synthesis problem in the SyGuS-supported subset.

    Solver-agnostic: both the textual SyGuS-IF emitter and the cvc5 API
    solver derive what they need from this.
    """

    fun_name: str
    params: list[SygusParam]
    ret_sort: str
    ret_base: TypeConstructor
    binder: Name  # the refined type's bound variable (the value being synthesised)
    refinement: LiquidTerm  # the specification phi, over ``binder`` and the params
    logic: str

    @property
    def is_real(self) -> bool:
        return self.ret_sort == "Real" or any(p.sort == "Real" for p in self.params)


def _smt_name(n: Name) -> str:
    """A legal SMT-LIB identifier that is stable for one Name.

    Aeon Names carry a disambiguating integer id; we keep it so two distinct
    binders never collide in the emitted text.
    """
    safe = "".join(c if (c.isalnum() or c == "_") else "_" for c in n.name)
    if not safe or not (safe[0].isalpha() or safe[0] == "_"):
        safe = "v_" + safe
    return f"{safe}_{n.id}"


def liquid_to_smt(t: LiquidTerm, names: dict[Name, str], is_real: bool) -> str | None:
    """Render a liquid term as an SMT-LIB S-expression, or None if unsupported.

    ``names`` maps the Aeon Names that may appear (params + binder) to their
    SMT-LIB identifiers.  Used for the textual (``.sl``) rendering.
    """
    match t:
        case LiquidLiteralBool(b):
            return "true" if b else "false"
        case LiquidLiteralInt(i):
            return str(i) if i >= 0 else f"(- {-i})"
        case LiquidLiteralFloat(f):
            lit = repr(float(abs(f)))
            return lit if f >= 0 else f"(- {lit})"
        case LiquidLiteralString():
            return None  # strings are outside the supported subset
        case LiquidVar(name):
            return names.get(name)
        case LiquidApp(fun, args):
            rendered = [liquid_to_smt(a, names, is_real) for a in args]
            if any(r is None for r in rendered):
                return None
            op = fun.name
            if op == "==":
                return f"(= {rendered[0]} {rendered[1]})"
            if op == "!=":
                return f"(not (= {rendered[0]} {rendered[1]}))"
            if op == "/":
                smt_op = "/" if is_real else "div"
                return f"({smt_op} {rendered[0]} {rendered[1]})"
            smt_op = _OP_TO_SMT.get(op)
            if smt_op is None:
                return None
            return f"({smt_op} {' '.join(rendered)})"
        case _:
            return None


def _hole_spec(ty: Type) -> tuple[TypeConstructor, Name, LiquidTerm] | None:
    """Return ``(base, binder, refinement)`` for a synthesisable hole type.

    Refined base types keep their predicate; bare ``Int`` / ``Bool`` /
    ``Float`` are treated as ``{v:T | true}``.
    """
    if isinstance(ty, RefinedType):
        ret_base = ty.type
        if not isinstance(ret_base, TypeConstructor):
            return None
        return ret_base, ty.name, ty.refinement
    if isinstance(ty, TypeConstructor):
        if ty not in _SORT_OF_BASE:
            return None
        binder = Name("_", fresh_counter.fresh())
        return ty, binder, LiquidLiteralBool(True)
    return None


def build_sygus_problem(ctx: TypingContext, ty: Type, fun_name: str = "f") -> SygusProblem | None:
    """Translate a hole type + context into a ``SygusProblem`` (or None).

    Supported subset: ``ty`` is a base SMT type (``Int``, ``Bool``, ``Float``)
    or a refinement ``{v:T | phi}`` over one of those, with ``phi`` built only
    from native operators over SMT-typed variables.
    """
    spec = _hole_spec(ty)
    if spec is None:
        return None
    ret_base, binder, refinement = spec
    ret_sort = smt_sort_of(ret_base)
    if ret_sort is None:
        return None

    spec_vars = set(liquid_free_vars(refinement))

    # Lift the SMT-typed context variables referenced by the spec into inputs.
    params: list[SygusParam] = []
    names: dict[Name, str] = {binder: _smt_name(binder)}
    for n, t in ctx.concrete_vars():
        if n == binder or n not in spec_vars:
            continue
        sort = smt_sort_of(t)
        if sort is None:
            continue
        smt_name = _smt_name(n)
        params.append(SygusParam(aeon_name=n, aeon_type=t, smt_name=smt_name, sort=sort))
        names[n] = smt_name

    # The spec must render to SMT-LIB end-to-end; bail out otherwise.
    is_real = ret_sort == "Real" or any(p.sort == "Real" for p in params)
    if liquid_to_smt(refinement, names, is_real) is None:
        return None

    # Any free var of the spec that is neither the binder nor a lifted param
    # is an unsupported reference (e.g. a non-SMT context value): fail.
    known = {binder} | {p.aeon_name for p in params}
    for v in spec_vars:
        if v in known:
            continue
        # Operators contribute their name to free vars but are not real refs.
        if v.name in _OP_TO_SMT or v.name in {"==", "!=", "/"}:
            continue
        return None

    logic = "NRA" if is_real else "NIA"
    return SygusProblem(
        fun_name=fun_name,
        params=params,
        ret_sort=ret_sort,
        ret_base=ret_base,
        binder=binder,
        refinement=refinement,
        logic=logic,
    )


def problem_to_sl(problem: SygusProblem) -> str:
    """Render a ``SygusProblem`` as SyGuS-IF (``.sl``) text.

    Universally quantifies the inputs and constrains the function so that the
    parameters' refinements imply the goal refinement.
    """
    # The binder is replaced by an application of the synthesised function.
    app = (
        problem.fun_name
        if not problem.params
        else f"({problem.fun_name} {' '.join(p.smt_name for p in problem.params)})"
    )
    names: dict[Name, str] = {problem.binder: app}
    for p in problem.params:
        names[p.aeon_name] = p.smt_name

    post = liquid_to_smt(problem.refinement, names, problem.is_real)
    assert post is not None  # build_sygus_problem already checked translatability

    pres: list[str] = []
    for p in problem.params:
        if isinstance(p.aeon_type, RefinedType):
            pre_names = dict(names)
            pre_names[p.aeon_type.name] = p.smt_name
            rendered = liquid_to_smt(p.aeon_type.refinement, pre_names, problem.is_real)
            if rendered is not None:
                pres.append(rendered)

    constraint = post if not pres else f"(=> {pres[0] if len(pres) == 1 else '(and ' + ' '.join(pres) + ')'} {post})"

    param_decl = " ".join(f"({p.smt_name} {p.sort})" for p in problem.params)
    lines = [
        f"(set-logic {problem.logic})",
        f"(synth-fun {problem.fun_name} ({param_decl}) {problem.ret_sort})",
    ]
    for p in problem.params:
        lines.append(f"(declare-var {p.smt_name} {p.sort})")
    lines.append(f"(constraint {constraint})")
    lines.append("(check-synth)")
    return "\n".join(lines) + "\n"
