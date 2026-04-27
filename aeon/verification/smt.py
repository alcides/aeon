from __future__ import annotations

from dataclasses import dataclass
from functools import reduce
from typing import Any
from typing import Generator
from loguru import logger

from z3 import Function
from z3 import Int
from z3 import Solver
from z3 import sat
from z3 import unknown
from z3.z3 import And
from z3.z3 import Bool
from z3.z3 import BoolRef
from z3.z3 import BoolSort
from z3.z3 import Const
from z3.z3 import DeclareSort
from z3.z3 import Float64
from z3.z3 import Implies
from z3.z3 import IntSort
from z3.z3 import Not
from z3.z3 import Or
from z3.z3 import String
from z3.z3 import StringSort
from z3.z3 import SortRef
from z3.z3types import Z3Exception

from aeon.core.liquid import LiquidApp
from aeon.core.types import LiquidHornApplication, TypeConstructor
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralFloat
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.liquid_ops import mk_liquid_and
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType, RefinedType, RefinementPolymorphism, Top, TypePolymorphism
from aeon.core.types import Type
from aeon.core.types import TypeVar
from aeon.core.types import t_bool, t_int, t_float, t_string, t_unit
from aeon.verification.sub import lower_constraint_type
from aeon.verification.vcs import Conjunction
from aeon.verification.vcs import alpha_key
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import Implication
from aeon.verification.vcs import LiquidConstraint
from aeon.verification.vcs import ReflectedFunctionDeclaration
from aeon.verification.vcs import UninterpretedFunctionDeclaration
from aeon.utils.name import Name, fresh_counter

smt_function_types: dict[str, list[Type]] = {
    "smtEqInt": [t_int, t_int, t_bool],
    "smtEqFloat": [t_float, t_float, t_bool],
    "smtEqBool": [t_float, t_float, t_bool],
    "smtEqString": [t_string, t_string, t_bool],
    "smtNeqInt": [t_int, t_int, t_bool],
    "smtNeqFloat": [t_float, t_float, t_bool],
    "smtNeqBool": [t_float, t_float, t_bool],
    "smtNeqString": [t_string, t_string, t_bool],
    "smtNot": [t_bool, t_bool],
    "smtLeqInt": [t_int, t_int, t_bool],
    "smtLeqFloat": [t_float, t_float, t_bool],
    "smtLtInt": [t_int, t_int, t_bool],
    "smtLtFloat": [t_float, t_float, t_bool],
    "smtAnd": [t_bool, t_bool, t_bool],
    "smtOr": [t_bool, t_bool, t_bool],
    "smtPlusInt": [t_int, t_int, t_int],
    "smtMinusInt": [t_int, t_int, t_int],
    "smtMultInt": [t_int, t_int, t_int],
    "smtDivInt": [t_int, t_int, t_int],
    "smtModInt": [t_int, t_int, t_int],
    "smtPlusFloat": [t_float, t_float, t_float],
    "smtMinusFloat": [t_float, t_float, t_float],
    "smtMultFloat": [t_float, t_float, t_float],
    "smtDivFloat": [t_float, t_float, t_float],
    "smtImplies": [t_bool, t_bool, t_bool],
}

smt_function_translation: dict[str, list[str]] = {
    "==": ["smtEqBool", "smtEqInt", "smtEqFloat", "smtEqString"],
    "!=": ["smtNeqBool", "smtNeqInt", "smtNeqFloat", "smtNeqString"],
    "!": ["smtNot"],
    "<": ["smtLeqInt", "smtLeqFloat"],
    "<=": ["smtLtInt", "smtLtFloat"],
    "&&": ["smtAnd"],
    "||": ["smtOr"],
    "+": ["smtPlusInt", "smtPlusFloat"],
    "-": ["smtMinusInt", "smtMinusFloat"],
    "*": ["smtMultInt", "smtMultFloat"],
    "/": ["smtDivInt", "smtDivFloat"],
    "%": ["smtModInt"],
    "-->": ["smtImplies"],
}

base_functions: dict[str, Any] = {
    "==": lambda x, y: x == y,
    "!=": lambda x, y: x != y,
    "<": lambda x, y: x < y,
    "<=": lambda x, y: x <= y,
    ">": lambda x, y: x > y,
    ">=": lambda x, y: x >= y,
    "!": lambda x: Not(x),
    "&&": lambda x, y: And(x, y),
    "||": lambda x, y: Or(x, y),
    "+": lambda x, y: x + y,
    "-": lambda x, y: x - y,
    "*": lambda x, y: x * y,
    "/": lambda x, y: x / y,
    "%": lambda x, y: x % y,
    "-->": lambda x, y: Implies(x, y),
}


@dataclass
class SMTContext:
    sorts: list[str]
    functions: dict[str, AbstractionType]
    variables: dict[str, TypeConstructor]
    premises: list[LiquidTerm]
    reflected_functions: dict[str, tuple[tuple[Name, ...], LiquidTerm]]

    def with_sort(self, name: Name) -> SMTContext:
        return SMTContext(
            self.sorts + [str(name)], self.functions, self.variables, self.premises, self.reflected_functions
        )

    def with_function(self, name: Name, ty: AbstractionType) -> SMTContext:
        return SMTContext(
            self.sorts, {**self.functions, str(name): ty}, self.variables, self.premises, self.reflected_functions
        )

    def with_var(self, name: Name, ty: TypeConstructor) -> SMTContext:
        return SMTContext(
            self.sorts, self.functions, {**self.variables, str(name): ty}, self.premises, self.reflected_functions
        )

    def with_premise(self, p: LiquidTerm) -> SMTContext:
        return SMTContext(self.sorts, self.functions, self.variables, self.premises + [p], self.reflected_functions)

    def with_reflected_function(self, name: Name, params: tuple[Name, ...], body: LiquidTerm) -> SMTContext:
        return SMTContext(
            self.sorts,
            self.functions,
            self.variables,
            self.premises,
            {**self.reflected_functions, str(name): (params, body)},
        )


def _ple_unfold_once(
    t: LiquidTerm,
    reflected_functions: dict[str, tuple[tuple[Name, ...], LiquidTerm]],
) -> tuple[LiquidTerm, bool]:
    match t:
        case LiquidApp(fun, args, loc):
            n_args: list[LiquidTerm] = []
            changed = False
            for arg in args:
                n_arg, arg_changed = _ple_unfold_once(arg, reflected_functions)
                n_args.append(n_arg)
                changed = changed or arg_changed
            key = str(fun)
            if key in reflected_functions:
                params, body = reflected_functions[key]
                if len(params) == len(n_args):
                    unfolded = body
                    for param, arg in zip(params, n_args):
                        unfolded = substitution_in_liquid(unfolded, arg, param)
                    return unfolded, True
            if changed:
                return LiquidApp(fun, n_args, loc=loc), True
            return t, False
        case _:
            return t, False


def ple_unfold_fixpoint(
    t: LiquidTerm,
    reflected_functions: dict[str, tuple[tuple[Name, ...], LiquidTerm]],
    max_steps: int = 256,
) -> LiquidTerm:
    def term_size(node: LiquidTerm) -> int:
        match node:
            case LiquidApp(_, args):
                return 1 + sum(term_size(a) for a in args)
            case _:
                return 1

    max_term_size = 4096
    current = t
    start_size = term_size(current)
    seen: set[str] = {repr(current)}
    unfolded_steps = 0
    stop_reason = "fixpoint"
    for _ in range(max_steps):
        current, changed = _ple_unfold_once(current, reflected_functions)
        if not changed:
            stop_reason = "no_change"
            break
        unfolded_steps += 1
        if term_size(current) > max_term_size:
            stop_reason = "size_guard"
            break
        signature = repr(current)
        if signature in seen:
            stop_reason = "seen_guard"
            break
        seen.add(signature)
    logger.debug(
        "PLE unfold: steps={} start_size={} final_size={} stop={} reflected_funs={}",
        unfolded_steps,
        start_size,
        term_size(current),
        stop_reason,
        len(reflected_functions),
    )
    return current


def _specialize_type(ty: Type, mapping: dict[str, TypeConstructor]) -> Type:
    match ty:
        case TypeConstructor(name, _, _):
            return mapping.get(name.name, ty)
        case AbstractionType(vname, vty, body, loc):
            svty = _specialize_type(vty, mapping)
            sbody = _specialize_type(body, mapping)
            assert isinstance(svty, (Top, TypeVar, TypeConstructor, RefinedType, AbstractionType))
            return AbstractionType(vname, svty, sbody, loc=loc)
        case TypePolymorphism(_, _, body):
            return _specialize_type(body, mapping)
        case RefinementPolymorphism(_, _, body):
            return _specialize_type(body, mapping)
        case RefinedType(vname, bty, ref, loc):
            sbty = _specialize_type(bty, mapping)
            assert isinstance(sbty, (TypeConstructor, TypeVar))
            return RefinedType(vname, sbty, ref, loc=loc)
        case _:
            return ty


def _term_base_type(t: LiquidTerm, variables: dict[str, TypeConstructor]) -> TypeConstructor | None:
    match t:
        case LiquidLiteralInt():
            return t_int
        case LiquidLiteralFloat():
            return t_float
        case LiquidLiteralBool():
            return t_bool
        case LiquidLiteralString():
            return t_string
        case LiquidVar(name):
            return variables.get(str(name), None)
        case _:
            return None


def _specialization_name(base: str, concrete: tuple[str, ...]) -> str:
    return f"{base}__spec__{'__'.join(concrete)}"


def _specialize_liquid_term(
    t: LiquidTerm,
    functions: dict[str, AbstractionType],
    variables: dict[str, TypeConstructor],
    reflected_functions: dict[str, tuple[tuple[Name, ...], LiquidTerm]],
    specializations: dict[tuple[str, tuple[str, ...]], str],
) -> tuple[LiquidTerm, dict[str, AbstractionType], dict[str, tuple[tuple[Name, ...], LiquidTerm]]]:
    if not isinstance(t, LiquidApp):
        return t, functions, reflected_functions

    nfuncs = functions
    nref = reflected_functions
    nargs: list[LiquidTerm] = []
    for a in t.args:
        sa, nfuncs, nref = _specialize_liquid_term(a, nfuncs, variables, nref, specializations)
        nargs.append(sa)

    fname = str(t.fun)
    if fname not in nfuncs:
        return LiquidApp(t.fun, nargs, loc=t.loc), nfuncs, nref

    fty = nfuncs[fname]
    cur: Type = fty
    subst: dict[str, TypeConstructor] = {}
    for arg in nargs:
        if not isinstance(cur, AbstractionType):
            break
        actual = _term_base_type(arg, variables)
        expected = cur.var_type
        if (
            isinstance(expected, TypeConstructor)
            and expected.name.name[:1].islower()
            and expected.name.name not in {"Int", "Bool", "Float", "String", "Unit", "Top"}
            and actual is not None
        ):
            subst[expected.name.name] = actual
        cur = cur.type

    if not subst:
        return LiquidApp(t.fun, nargs, loc=t.loc), nfuncs, nref

    concrete_sig = tuple(sorted(str(v.name) for v in subst.values()))
    skey = (fname, concrete_sig)
    if skey in specializations:
        sname = specializations[skey]
    else:
        sname = _specialization_name(fname, concrete_sig)
        nty = _specialize_type(fty, subst)
        assert isinstance(nty, AbstractionType)
        nfuncs = {**nfuncs, sname: nty}
        if fname in nref:
            nref = {**nref, sname: nref[fname]}
        specializations[skey] = sname
    return LiquidApp(Name(sname, 0), nargs, loc=t.loc), nfuncs, nref


def _ctx_with_curried_formals(ctx: SMTContext, fun_ty: AbstractionType) -> SMTContext:
    """Add Z3-scalar bindings for each curried parameter of ``fun_ty`` (for UFD / recursion VCs)."""
    out = ctx
    cur: Type = fun_ty
    while isinstance(cur, AbstractionType):
        base = lower_constraint_type(cur.var_type)
        match base:
            case TypeVar(iname):
                base_tc = TypeConstructor(iname)
            case TypeConstructor(iname, []):
                base_tc = base
            case TypeConstructor(iname, args):
                mangle_name = str(iname) + "_" + "_".join(str(a) for a in args)
                nname = Name(mangle_name, fresh_counter.fresh())
                base_tc = TypeConstructor(nname)
            case AbstractionType(_, _, _) | TypePolymorphism(_, _, _) | RefinementPolymorphism(_, _, _):
                # Higher-rank arguments are represented as opaque scalar tokens in SMT.
                base_tc = t_int
            case _:
                assert False, f"{base} ({type(base)}) is not a base type for curried formal."
        out = out.with_var(cur.var_name, base_tc)
        cur = cur.type
    return out


@dataclass(init=False)
class CanonicConstraint:
    """Represents SMT-valid constraints."""

    sorts: list[str]
    functions: dict[str, AbstractionType]
    variables: dict[str, TypeConstructor]
    premise: LiquidTerm
    conclusion: LiquidTerm

    def __init__(self, ctx: SMTContext, pos: LiquidTerm):
        self.sorts = ctx.sorts
        self.functions = ctx.functions
        self.variables = ctx.variables
        self.premise = reduce(mk_liquid_and, ctx.premises, LiquidLiteralBool(True))
        self.conclusion = pos


def rename_constraint(c: Constraint, old_name: Name, new_name: Name) -> Constraint:
    """Renames a binder within the constraint, to make it is unique."""
    match c:
        case LiquidConstraint(expr):
            nexpr = substitution_in_liquid(expr, LiquidVar(new_name), old_name)
            return LiquidConstraint(expr=nexpr)
        case Conjunction(c1, c2):
            return Conjunction(rename_constraint(c1, old_name, new_name), rename_constraint(c2, old_name, new_name))
        case Implication(name, base, pred, seq):
            if name == new_name:
                return c
            else:
                npred = substitution_in_liquid(pred, LiquidVar(new_name), old_name)
                nseq = rename_constraint(seq, old_name, new_name)
                return Implication(name, base, npred, nseq)
        case UninterpretedFunctionDeclaration(name, absty, seq):
            nseq = rename_constraint(seq, old_name, new_name)
            return UninterpretedFunctionDeclaration(name, absty, nseq)
        case ReflectedFunctionDeclaration(name, absty, params, body, seq):
            nbody = substitution_in_liquid(body, LiquidVar(new_name), old_name)
            nparams = tuple(new_name if p == old_name else p for p in params)
            nseq = rename_constraint(seq, old_name, new_name)
            return ReflectedFunctionDeclaration(name, absty, nparams, nbody, nseq)
        case _:
            assert False, f"Unexpected case {c} ({type(c)})"


def flatten(c: Constraint, ctx: SMTContext | None = None) -> Generator[CanonicConstraint]:
    """Flattens a constraint into a list of SMT-valid constraints."""
    if ctx is None:
        ctx = SMTContext(["Top"], {}, {}, [], {})
    match c:
        case LiquidConstraint(expr):
            specializations: dict[tuple[str, tuple[str, ...]], str] = {}
            nfunctions = ctx.functions
            nref = ctx.reflected_functions
            sprem: list[LiquidTerm] = []
            for p in ctx.premises:
                sp, nfunctions, nref = _specialize_liquid_term(p, nfunctions, ctx.variables, nref, specializations)
                sprem.append(sp)
            sexpr, nfunctions, nref = _specialize_liquid_term(expr, nfunctions, ctx.variables, nref, specializations)
            premise = [ple_unfold_fixpoint(p, nref) for p in sprem]
            out_ctx = SMTContext(ctx.sorts, nfunctions, ctx.variables, premise, nref)
            yield CanonicConstraint(out_ctx, ple_unfold_fixpoint(sexpr, nref))
        case Conjunction(c1, c2):
            yield from flatten(c1, ctx)
            yield from flatten(c2, ctx)
        case Implication(oname, base, pred, seq):
            name = Name(oname.name, fresh_counter.fresh())
            pred = substitution_in_liquid(pred, LiquidVar(name), oname)
            seq = rename_constraint(seq, oname, name)
            match base:
                case TypeVar(iname):
                    base = TypeConstructor(iname)
                case TypeConstructor(iname, []):
                    pass
                case TypeConstructor(iname, args):
                    mangle_name = str(iname) + "_" + "_".join(str(a) for a in args)
                    nname = Name(mangle_name, fresh_counter.fresh())
                    base = TypeConstructor(nname)
                case _:
                    assert False, f"{base} ({type(base)}) is not a base type."
            yield from flatten(seq, ctx.with_var(name, base).with_premise(pred))
        case UninterpretedFunctionDeclaration(name, ty, seq):
            assert isinstance(c, UninterpretedFunctionDeclaration)
            nctx = _ctx_with_curried_formals(ctx, ty)
            yield from flatten(seq, nctx.with_function(name, ty))
        case ReflectedFunctionDeclaration(name, ty, params, body, seq):
            nctx = (
                _ctx_with_curried_formals(ctx, ty).with_function(name, ty).with_reflected_function(name, params, body)
            )
            app = LiquidApp(name, [LiquidVar(p) for p in params])
            eq = LiquidApp(Name("==", 0), [app, body])
            yield from flatten(seq, nctx.with_premise(eq))
        case _:
            assert False, f"Cannot flatten {c}."


s = Solver()
(s.set(timeout=200),)

_smt_valid_cache: dict[str, bool] = {}


def smt_valid(constraint: Constraint) -> bool:
    """Verifies if a constraint is true using Z3."""
    key = alpha_key(constraint)
    cached = _smt_valid_cache.get(key)
    if cached is not None:
        return cached

    n = 0
    for c in flatten(constraint):
        n += 1
        s.push()

        # TODO now: Add monomorphic, uncurried functions here
        try:
            smt_c = translate(c)
        except ZeroDivisionError:
            continue
        if smt_c is False:
            continue
        s.add(smt_c)
        result = s.check()
        s.pop()
        if result == sat:
            _smt_valid_cache[key] = False
            return False
        elif result == unknown:
            _smt_valid_cache[key] = False
            return False

    _smt_valid_cache[key] = True
    return True


def type_of_variable(variables: list[tuple[str, Any]], name: str) -> Any:
    for na, ref in reversed(variables):
        if na == name:
            return ref
    vars = ", ".join([x[0] for x in variables])
    logger.error(f"No variable {name} in the context: {vars}")
    assert False


sort_cache: dict[str, SortRef] = {}


def mk_vars(variables: dict[str, TypeConstructor], sorts: dict[str, SortRef]) -> dict[str, Any]:
    return {name: make_variable(name, base) for name, base in variables.items()}


def get_sort(base: Type) -> SortRef:
    match base:
        case Top() | TypeConstructor(Name("Top", _)):
            return DeclareSort("Top")
        case TypeConstructor(Name("Int", _)):
            return IntSort()
        case TypeConstructor(Name("Bool", _)):
            return BoolSort()
        case TypeConstructor(Name("Float", _)):
            return Float64()
        case TypeConstructor(Name("String", _)):
            return StringSort()
        case TypeConstructor(name, _):
            return IntSort()
            # This will be reenable once we have typeclasses
            # if name not in sort_cache:
            #     sort_cache[name] = DeclareSort(name)
            # return sort_cache[name]
        case TypeVar(name):
            assert False, f"TypeVar {name} should not be used in SMT solver."
        case _:
            raise Exception(f"SMT sort of {base} not implemented.")


def unrefine_type(base: Type):
    """Removes refinements from type."""
    match base:
        case RefinedType(_, ty, _):
            return ty
        case AbstractionType(name, aty, rty):
            return AbstractionType(name, unrefine_type(aty), unrefine_type(rty))
        case TypePolymorphism(name, kind, body):
            return TypePolymorphism(name, kind, unrefine_type(body))
        case TypeConstructor(name, args):
            return TypeConstructor(name, [unrefine_type(a) for a in args])

        case _:
            return base


def uncurry(base: AbstractionType) -> tuple[list[TypeConstructor], TypeConstructor]:
    current: Type = unrefine_type(base)
    inputs = []
    vars_to_remove = []

    while isinstance(current, TypePolymorphism):
        vars_to_remove.append(current.name)
        current = current.body

    while isinstance(current, AbstractionType):
        match current.var_type:
            case TypeConstructor(_, []):
                inputs.append(current.var_type)
            case TypeConstructor(_, _):
                inputs.append(t_int)
            case Top():
                inputs.append(t_unit)
            case TypeVar(name):
                if name in vars_to_remove:
                    inputs.append(t_int)
                else:
                    inputs.append(TypeConstructor(name))
            case AbstractionType(_, _, _) | TypePolymorphism(_, _, _) | RefinementPolymorphism(_, _, _):
                inputs.append(t_int)
            case _:
                assert False, f"Unknown SMT type {current.var_type} in {base}."
        current = current.type

    if isinstance(current, Top):
        current = t_unit
    assert isinstance(current, TypeConstructor), f"Unknown SMT type {current} in {base}."
    return (inputs, current)


def make_variable(name: str, base: TypeConstructor | AbstractionType | Top) -> Any:
    match base:
        case Top():
            return Const(name, get_sort(base))
        case TypeConstructor(Name("Int", _)):
            return Int(name)
        case TypeConstructor(Name("Bool", _)):
            return Bool(name)
        case TypeConstructor(Name("Float", _), _):
            import z3

            v = z3.Real(name)
            return v
            # TODO: see problem with version below
            # fpsort = FPSort(8, 24)
            # return FP(name, fpsort)
        case TypeConstructor(Name("String", _)):
            return String(name)
        case TypeConstructor(_, _):
            return Int(name)
            # TODO: we always use int, in the case of a typevar.
            # return Const(name, get_sort(base))
        case TypeVar(_):
            return Int(name)
        case AbstractionType(_, _, _):
            if name in base_functions:
                return base_functions[name]
            else:
                input_types, output_type = uncurry(base)
                args = [get_sort(x) for x in input_types] + [get_sort(output_type)]
                return Function(name, *args)
        case _:
            assert False, f"No var: {name}, with base {base}."


def translate_liq(t: LiquidTerm, variables: dict[str, Any]):
    match t:
        case LiquidLiteralBool(b):
            return b
        case LiquidLiteralInt(i):
            return i
        case LiquidLiteralFloat(f):
            return f
        case LiquidLiteralString(s):
            return s
        case LiquidVar(name):
            return variables[str(name)]
        case LiquidHornApplication(name, args):
            assert False, "LiquidHornApplication should not get to SMT solver!"
        case LiquidApp(fun_name, args):
            fun = base_functions.get(fun_name.name, variables.get(str(fun_name), None))
            assert fun is not None, f"Function {fun_name} not found." + str(variables)
            args = [translate_liq(a, variables) for a in args]
            try:
                return fun(*args)
            except Z3Exception as e:
                raise e

        case _:
            assert False, f"Cannot translate {t}."


def mk_sorts(sorts: list[str]) -> dict[str, SortRef]:
    return {name: get_sort(TypeConstructor(Name(name, 0))) for name in sorts}


def mk_funs(functions: dict[str, AbstractionType], sorts: dict[str, SortRef]) -> dict[str, Any]:
    funs = {}
    for name, ty in functions.items():
        input_types, output_type = uncurry(ty)
        args = [sorts.get(str(x), get_sort(x)) for x in input_types] + [
            sorts.get(str(output_type), get_sort(output_type))
        ]
        funs[name] = Function(name, *args)
    return funs


def translate(
    c: CanonicConstraint,
) -> BoolRef | bool:
    sorts = mk_sorts(c.sorts)
    functions = mk_funs(c.functions, sorts)
    variables = mk_vars(c.variables, sorts)
    e1 = translate_liq(c.premise, variables | functions)
    e2 = translate_liq(c.conclusion, variables | functions)
    if isinstance(e2, bool) and e2 is True:
        return False
    if isinstance(e1, bool) and isinstance(e2, bool):
        return e1 and not e2
    return And(e1, Not(e2))
