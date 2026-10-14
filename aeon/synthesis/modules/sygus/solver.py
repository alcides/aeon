"""Phases 2 & 3 of issue #49: solve a ``SygusProblem`` with cvc5.

The synthesis problem is built directly through the cvc5 SyGuS Python API
(``synthFun`` / ``declareSygusVar`` / ``addSygusConstraint`` / ``checkSynth``
/ ``getSynthSolution``) — no SyGuS-IF text is shipped to a subprocess.  The
cvc5 ``Term`` that comes back is then walked into a well-typed Aeon-core
``Term`` (the issue's phase 3).

cvc5 is imported lazily and only here: the rest of the project never touches
this API, and a missing cvc5 turns into a clean ``SynthesisNotSuccessful``
in the synthesizer rather than an import-time crash.
"""

from __future__ import annotations

from typing import Any

from aeon.core.terms import Application, If, Literal, Term, TypeApplication, Var
from aeon.core.types import RefinedType, TypeConstructor, t_bool, t_float, t_int
from aeon.synthesis.modules.sygus.translation import SygusProblem
from aeon.utils.name import Name


class CVC5Unavailable(Exception):
    """Raised when the cvc5 Python bindings cannot be imported."""


def _import_cvc5() -> Any:
    try:
        import cvc5  # noqa: PLC0415  (lazy, kept local to this backend)

        return cvc5
    except ImportError as exc:  # pragma: no cover - environment dependent
        raise CVC5Unavailable(
            "cvc5 Python bindings are not installed; `pip install cvc5` to use the sygus backend",
        ) from exc


# ---------------------------------------------------------------------------
# Aeon-core term construction helpers
# ---------------------------------------------------------------------------


def _apply_op(sym: str, base: TypeConstructor, *args: Term) -> Term:
    """Build ``sym`` applied to ``args`` as a native (polymorphic) operator."""
    out: Term = TypeApplication(Var(Name(sym, 0)), base)
    for a in args:
        out = Application(out, a)
    return out


def _num_literal(value: int | float, base: TypeConstructor) -> Term:
    """A possibly-negative numeric literal.

    Aeon has no negative-literal syntax, so negatives are emitted as ``0 - n``
    (mirroring ``examples/synthesis/quadratic.ae``).
    """
    if base == t_float:
        value = float(value)
        zero: int | float = 0.0
    else:
        value = int(value)
        zero = 0
    if value >= 0:
        return Literal(value, base)
    return _apply_op("-", base, Literal(zero, base), Literal(-value, base))


# ---------------------------------------------------------------------------
# cvc5 solving
# ---------------------------------------------------------------------------


def _base_of_sort(sort: str) -> TypeConstructor:
    return t_float if sort == "Real" else (t_bool if sort == "Bool" else t_int)


def _liquid_to_cvc5(t: Any, env: dict[Name, Any], slv: Any, kinds: Any, is_real: bool) -> Any:
    """Translate a liquid refinement term into a cvc5 ``Term``.

    ``env`` maps the Aeon Names that may appear (params + binder) to their
    cvc5 terms.  Raises on anything unsupported; the caller guards with the
    same subset check ``build_sygus_problem`` already enforced.
    """
    from aeon.core.liquid import (
        LiquidApp,
        LiquidLiteralBool,
        LiquidLiteralFloat,
        LiquidLiteralInt,
        LiquidVar,
    )

    Kind = kinds
    binary = {
        "<": Kind.LT,
        "<=": Kind.LEQ,
        ">": Kind.GT,
        ">=": Kind.GEQ,
        "&&": Kind.AND,
        "||": Kind.OR,
        "-->": Kind.IMPLIES,
        "+": Kind.ADD,
        "-": Kind.SUB,
        "*": Kind.MULT,
        "%": Kind.INTS_MODULUS,
        "==": Kind.EQUAL,
    }
    match t:
        case LiquidLiteralBool(b):
            return slv.mkBoolean(bool(b))
        case LiquidLiteralInt(i):
            return slv.mkInteger(int(i))
        case LiquidLiteralFloat(f):
            return slv.mkReal(str(float(f)))
        case LiquidVar(name):
            if name not in env:
                raise ValueError(f"unbound variable {name} in spec")
            return env[name]
        case LiquidApp(fun, args):
            cargs = [_liquid_to_cvc5(a, env, slv, kinds, is_real) for a in args]
            op = fun.name
            if fun in env:
                return slv.mkTerm(Kind.APPLY_UF, env[fun], *cargs)
            if op == "ite":
                return slv.mkTerm(Kind.ITE, *cargs)
            if op == "!":
                return slv.mkTerm(Kind.NOT, cargs[0])
            if op == "!=":
                return slv.mkTerm(Kind.DISTINCT, cargs[0], cargs[1])
            if op == "/":
                return slv.mkTerm(
                    Kind.INTS_DIVISION if cargs[0].getSort().isInteger() else Kind.DIVISION, cargs[0], cargs[1]
                )
            if op in binary:
                return slv.mkTerm(binary[op], *cargs)
            raise ValueError(f"unsupported operator {op} in spec")
        case _:
            raise ValueError(f"cannot translate liquid term {t}")


def solve_with_cvc5(problem: SygusProblem, timeout_ms: int) -> Term | None:
    """Solve a ``SygusProblem`` with cvc5 and return an Aeon-core term, or None."""
    cvc5 = _import_cvc5()
    Kind = cvc5.Kind

    slv = cvc5.Solver()
    slv.setOption("sygus", "true")
    slv.setOption("tlimit", str(max(1, timeout_ms)))
    try:
        slv.setLogic(problem.logic)
    except Exception:
        slv.setLogic("ALL")

    def sort_of(name: str) -> Any:
        return {
            "Int": slv.getIntegerSort(),
            "Bool": slv.getBooleanSort(),
            "Real": slv.getRealSort(),
        }[name]

    # synth-fun f ((p Sort)...) RetSort   — the formal arguments are mkVars.
    arg_vars = [slv.mkVar(sort_of(p.sort), p.smt_name) for p in problem.params]
    f = slv.synthFun(problem.fun_name, arg_vars, sort_of(problem.ret_sort))

    # declare-var for each universally-quantified spec variable, and the
    # application of the synthesised function that replaces the binder.
    env: dict[Name, Any] = {}
    decl_vars: list[Any] = []
    for p in problem.params:
        v = slv.declareSygusVar(p.smt_name, sort_of(p.sort))
        env[p.aeon_name] = v
        decl_vars.append(v)
    f_app = f if not decl_vars else slv.mkTerm(Kind.APPLY_UF, f, *decl_vars)
    env[problem.binder] = f_app

    # Preconditions (input refinements) imply the goal refinement.
    try:
        post = _liquid_to_cvc5(problem.refinement, env, slv, Kind, problem.is_real)
        pres: list[Any] = []
        for p, v in zip(problem.params, decl_vars):
            if isinstance(p.aeon_type, RefinedType):
                pre_env = dict(env)
                pre_env[p.aeon_type.name] = v
                pres.append(_liquid_to_cvc5(p.aeon_type.refinement, pre_env, slv, Kind, problem.is_real))
    except ValueError:
        return None

    if not pres:
        constraint = post
    else:
        antecedent = pres[0] if len(pres) == 1 else slv.mkTerm(Kind.AND, *pres)
        constraint = slv.mkTerm(Kind.IMPLIES, antecedent, post)
    slv.addSygusConstraint(constraint)

    try:
        result = slv.checkSynth()
    except Exception:
        return None
    if not result.hasSolution():
        return None

    solution = slv.getSynthSolution(f)
    return _cvc5_solution_to_term(solution, problem, Kind)


# ---------------------------------------------------------------------------
# cvc5 Term -> Aeon-core Term (phase 3)
# ---------------------------------------------------------------------------


def _cvc5_solution_to_term(solution: Any, problem: SygusProblem, Kind: Any) -> Term | None:
    """Translate the cvc5 synthesis answer into an Aeon-core term.

    For an n-ary function the answer is ``(lambda (vars...) body)``; for a
    nullary one it is the body directly.
    """
    varmap: dict[Any, Name] = {}
    if solution.getKind() == Kind.LAMBDA:
        var_list = list(solution[0])
        for cvc_var, param in zip(var_list, problem.params):
            varmap[cvc_var] = param.aeon_name
        body = solution[1]
    else:
        body = solution
    try:
        return _cvc5_term_to_core(body, varmap, problem, Kind)
    except (ValueError, KeyError):
        return None


def _cvc5_term_to_core(node: Any, varmap: dict[Any, Name], problem: SygusProblem, Kind: Any) -> Term:
    base = _base_of_sort(str(node.getSort()))
    kind = node.getKind()
    if node.getNumChildren() and kind != Kind.ITE:
        base = _base_of_sort(str(node[0].getSort()))

    # Leaves -----------------------------------------------------------------
    if kind == Kind.CONST_INTEGER:
        return _num_literal(node.getIntegerValue(), t_int)
    if kind == Kind.CONST_BOOLEAN:
        return Literal(node.getBooleanValue(), t_bool)
    if kind == Kind.CONST_RATIONAL:
        value = node.getRealValue()
        if value.denominator == 1:
            return _num_literal(value.numerator, t_float)
        return _apply_op("/", t_float, _num_literal(value.numerator, t_float), _num_literal(value.denominator, t_float))
    if kind == Kind.VARIABLE:
        if node not in varmap:
            raise ValueError(f"unmapped variable {node}")
        return Var(varmap[node])

    children = [_cvc5_term_to_core(c, varmap, problem, Kind) for c in node]

    # Operators --------------------------------------------------------------
    if kind == Kind.NEG:  # unary minus -> 0 - x
        zero = Literal(0.0 if base == t_float else 0, base)
        return _apply_op("-", base, zero, children[0])
    if kind == Kind.ITE:
        return If(children[0], children[1], children[2])
    if kind == Kind.DISTINCT:
        return _apply_op("!=", base, children[0], children[1])

    binary_op = {
        Kind.ADD: "+",
        Kind.SUB: "-",
        Kind.MULT: "*",
        Kind.INTS_DIVISION: "/",
        Kind.DIVISION: "/",
        Kind.INTS_MODULUS: "%",
        Kind.LT: "<",
        Kind.LEQ: "<=",
        Kind.GT: ">",
        Kind.GEQ: ">=",
        Kind.EQUAL: "==",
        Kind.AND: "&&",
        Kind.OR: "||",
        Kind.IMPLIES: "-->",
    }
    if kind == Kind.NOT:
        return _apply_op("!", base, children[0])
    op = binary_op.get(kind)
    if op is None:
        raise ValueError(f"unsupported cvc5 kind {kind}")
    # cvc5 emits variadic and/or/+/* ; fold left into binary applications.
    result = _apply_op(op, base, children[0], children[1])
    for extra in children[2:]:
        result = _apply_op(op, base, result, extra)
    return result


def _solve_joint_cvc5(problem, timeout_ms):
    """Declare every unknown before adding shared constraints and checking once."""
    from aeon.core.liquid import LiquidLiteralBool
    from aeon.core.substitutions import substitution
    from aeon.synthesis.api import SynthesisNotSuccessful
    from aeon.synthesis.joint import JointCandidate
    from aeon.synthesis.modules.sygus.translation import SygusParam, smt_sort_of
    from aeon.utils.name import fresh_counter

    cvc5 = _import_cvc5()
    slv = cvc5.Solver()
    slv.setOption("sygus", "true")
    slv.setOption("tlimit", str(max(1, timeout_ms)))
    slv.setLogic("ALL")
    sorts = {t_int: slv.getIntegerSort(), t_bool: slv.getBooleanSort(), t_float: slv.getRealSort()}
    functions, descriptions = {}, []
    for hole in problem.holes:
        params = hole.params or ((Name("unused", fresh_counter.fresh()), t_int),)
        formals = [slv.mkVar(sorts[base], str(name)) for name, base in params]
        functions[hole.symbol] = slv.synthFun(str(hole.symbol), formals, sorts[hole.base])
        descriptions.append(
            SygusProblem(
                str(hole.symbol),
                [SygusParam(name, base, str(name), smt_sort_of(base)) for name, base in params],
                smt_sort_of(hole.base),
                hole.base,
                hole.symbol,
                LiquidLiteralBool(True),
                "ALL",
            )
        )
    for index, clause in enumerate(problem.clauses):
        env = dict(functions)
        for name, base in clause.variables:
            env[name] = slv.declareSygusVar(f"{name}_clause_{index}", sorts[base])
        premise = _liquid_to_cvc5(clause.premise, env, slv, cvc5.Kind, False)
        conclusion = _liquid_to_cvc5(clause.conclusion, env, slv, cvc5.Kind, False)
        slv.addSygusConstraint(slv.mkTerm(cvc5.Kind.IMPLIES, premise, conclusion))
    result = slv.checkSynth()
    if not result.hasSolution():
        raise SynthesisNotSuccessful(f"Joint SyGuS: {result}")
    solutions = slv.getSynthSolutions(list(functions.values()))
    terms = []
    for hole, description, solution in zip(problem.holes, descriptions, solutions):
        body = _cvc5_solution_to_term(solution, description, cvc5.Kind)
        if body is None:
            raise SynthesisNotSuccessful("Joint SyGuS cannot translate every solution")
        if hole.dummy:
            body = substitution(body, Literal(0, t_int), description.params[0].aeon_name)
        terms.append(hole.wrap(body))
    if len(terms) != len(problem.holes):
        raise SynthesisNotSuccessful("Joint SyGuS returned an incomplete assignment")
    return JointCandidate(tuple(terms))


def _clear_type_hashes(value):
    # TypeConstructor caches Python hashes, which differ between spawn workers.
    # Never retain those process-local caches across the IPC boundary.
    from dataclasses import fields, is_dataclass

    if isinstance(value, TypeConstructor) and hasattr(value, "_hash"):
        object.__delattr__(value, "_hash")
    if is_dataclass(value):
        for field in fields(value):
            _clear_type_hashes(getattr(value, field.name))
    elif isinstance(value, (tuple, list)):
        for item in value:
            _clear_type_hashes(item)


def _joint_worker(problem, timeout_ms, connection):
    try:
        _clear_type_hashes(problem)
        result = _solve_joint_cvc5(problem, timeout_ms)
        _clear_type_hashes(result)
        connection.send((True, result))
    except Exception as exc:
        connection.send((False, str(exc)))
    finally:
        connection.close()


def solve_joint_cvc5(problem, timeout_ms):
    """Bound native cvc5 execution even when its internal time limit is ignored."""
    import multiprocessing
    import time
    from aeon.synthesis.api import SynthesisNotSuccessful

    started = time.monotonic()
    context = multiprocessing.get_context("spawn")
    reader, writer = context.Pipe(duplex=False)
    process = context.Process(target=_joint_worker, args=(problem, timeout_ms, writer))
    process.start()
    writer.close()
    try:
        remaining = max(0, timeout_ms / 1000 - (time.monotonic() - started))
        if not reader.poll(remaining):
            raise SynthesisNotSuccessful("Joint SyGuS: time budget exhausted")
        try:
            success, value = reader.recv()
        except EOFError as exc:
            raise SynthesisNotSuccessful("Joint SyGuS: solver process exited without a result") from exc
        if not success:
            raise SynthesisNotSuccessful(value)
        return value
    finally:
        reader.close()
        if process.is_alive():
            process.terminate()
        process.join(timeout=1)
        if process.is_alive():
            process.kill()
            process.join()
        process.close()
