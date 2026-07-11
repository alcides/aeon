from __future__ import annotations

from functools import reduce
from typing import Callable, Generator, cast

from aeon.core.liquid import liquid_free_vars
from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralFloat
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidLiteralUnit
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import liquefy
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType, TypeConstructor, Top, TypeVar
from aeon.core.types import t_bool
from aeon.core.parser import parse_term
from aeon.verification.smt import base_functions
from aeon.verification.vcs import Conjunction
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import Implication
from aeon.verification.vcs import LiquidConstraint
from aeon.verification.vcs import ReflectedFunctionDeclaration
from aeon.verification.vcs import UninterpretedFunctionDeclaration
from aeon.utils.location import Location
from aeon.utils.name import Name, fresh_counter


def constraint_location(c: Constraint) -> Location | None:
    """Recursively extracts the first non-None location from a constraint."""
    match c:
        case LiquidConstraint(loc=loc):
            return loc
        case Implication(loc=loc, seq=seq):
            return loc or constraint_location(seq)
        case Conjunction(loc=loc, c1=c1, c2=c2):
            return loc or constraint_location(c1) or constraint_location(c2)
        case UninterpretedFunctionDeclaration(seq=seq):
            return constraint_location(seq)
        case ReflectedFunctionDeclaration(seq=seq):
            return constraint_location(seq)
        case _:
            return None


def parse_liquid(t: str) -> LiquidTerm | None:
    tp = parse_term(t)
    tl = liquefy(tp)
    return tl


def imp(a: str | LiquidTerm, b: Constraint) -> Constraint:
    match a:
        case LiquidTerm():
            e = a
        case str():
            e = parse_liquid(a)
    assert e is not None
    return Implication(Name("_", fresh_counter.fresh()), t_bool, e, b)


def conj(a: Constraint, b: Constraint) -> Constraint:
    return Conjunction(a, b)


def end(a: str | LiquidTerm) -> LiquidConstraint:
    match a:
        case LiquidTerm():
            e = a
        case str():
            e = parse_liquid(a)
    assert e is not None
    return LiquidConstraint(e)


def constraint_builder(vs: list[tuple[Name, TypeConstructor | TypeVar | AbstractionType | Top]], exp: Constraint):
    for n, t in vs[::-1]:
        match t:
            case AbstractionType():
                exp = UninterpretedFunctionDeclaration(n, t, exp)
            case _:
                exp = Implication(n, t, LiquidLiteralBool(True), exp)
    return exp


def simplify_is_true(c: Constraint):
    match c:
        case LiquidConstraint(expr=expr):
            return expr == LiquidLiteralBool(True)
        case _:
            return False


def flatten_conjunctions(c: Conjunction) -> list[Constraint]:
    queue = [c.c1, c.c2]
    conjunctions = []

    while queue:
        o = queue.pop()
        match o:
            case Conjunction(c1=o1, c2=o2):
                queue.append(o1)
                queue.append(o2)
            case _ if simplify_is_true(o):
                pass
            case _:
                conjunctions.append(o)
    return conjunctions


def is_used_liquid(n: Name, c: LiquidTerm) -> bool:
    return n in liquid_free_vars(c)


def is_used(n: Name, c: Constraint) -> bool:
    match c:
        case LiquidConstraint(expr=expr):
            return is_used_liquid(n, expr)
        case UninterpretedFunctionDeclaration():
            return False
        case ReflectedFunctionDeclaration(body=body, seq=seq):
            return is_used_liquid(n, body) or is_used(n, seq)
        case Implication(name=iname, pred=pred, seq=seq):
            if n == iname:
                return False
            return is_used_liquid(n, pred) or is_used(n, seq)
        case Conjunction(c1=c1, c2=c2):
            return is_used(n, c1) or is_used(n, c2)
        case _:
            assert False, f"Unsupported Constraint: {c}"


def flatten_conjuncts(expr: LiquidTerm) -> list[LiquidTerm]:
    """Flattens a conjunction into a list of conjuncts."""
    match expr:
        case LiquidApp(fun=f, args=[a0, a1]) if f == Name("&&", 0):
            return flatten_conjuncts(a0) + flatten_conjuncts(a1)
        case LiquidLiteralBool(True):
            return []
        case _:
            return [expr]


def rebuild_conjunction(conjuncts: list[LiquidTerm]) -> LiquidTerm:
    """Rebuilds a conjunction from a list of conjuncts."""
    if not conjuncts:
        return LiquidLiteralBool(True)
    result = conjuncts[0]
    for c in conjuncts[1:]:
        result = LiquidApp(Name("&&", 0), [result, c])
    return result


def with_location(term: LiquidTerm, loc: Location) -> LiquidTerm:
    """Return a shallow copy of *term* whose `loc` field is *loc*."""
    match term:
        case LiquidLiteralBool(value):
            return LiquidLiteralBool(value, loc=loc)
        case LiquidLiteralInt(value):
            return LiquidLiteralInt(value, loc=loc)
        case LiquidLiteralFloat(value):
            return LiquidLiteralFloat(value, loc=loc)
        case LiquidLiteralString(value):
            return LiquidLiteralString(value, loc=loc)
        case LiquidLiteralUnit():
            return LiquidLiteralUnit(loc=loc)
        case LiquidVar(name):
            return LiquidVar(name, loc=loc)
        case LiquidApp(fun, args):
            return LiquidApp(fun, args, loc=loc)
        case _:
            return term


def substitution_in_liquid_with_loc(t: LiquidTerm, rep: LiquidTerm, name: Name) -> LiquidTerm:
    """Like ``substitution_in_liquid`` but the replacement inherits the source
    location of each replaced ``LiquidVar``, so error messages point to the
    original variable usage site rather than the literal that replaced it."""
    match t:
        case (
            LiquidLiteralBool(_)
            | LiquidLiteralInt(_)
            | LiquidLiteralFloat(_)
            | LiquidLiteralString(_)
            | LiquidLiteralUnit()
        ):
            return t
        case LiquidVar(tname, loc):
            if tname == name:
                return with_location(rep, loc)
            return t
        case LiquidApp(aname, args, loc):
            nargs = [substitution_in_liquid_with_loc(a, rep, name) for a in args]
            if aname == name:
                assert isinstance(rep, LiquidVar)
                return LiquidApp(rep.name, nargs, loc=loc)
            return LiquidApp(aname, nargs, loc=loc)
        case _:
            return substitution_in_liquid(t, rep, name)


def substitution_in_constraint_with_loc(c: Constraint, rep: LiquidTerm, name: Name) -> Constraint:
    """Constraint-level wrapper for ``substitution_in_liquid_with_loc``."""
    match c:
        case LiquidConstraint(expr):
            return LiquidConstraint(substitution_in_liquid_with_loc(expr, rep, name), loc=c.loc)
        case Conjunction(c1, c2):
            left = substitution_in_constraint_with_loc(c1, rep, name)
            right = substitution_in_constraint_with_loc(c2, rep, name)
            return Conjunction(left, right, loc=c.loc)
        case Implication(impl_name, base, pred, seq):
            if name == impl_name:
                return c
            nseq = substitution_in_constraint_with_loc(seq, rep, name)
            return Implication(impl_name, base, substitution_in_liquid_with_loc(pred, rep, name), nseq, loc=c.loc)
        case UninterpretedFunctionDeclaration(ufd_name, ufd_type, seq):
            nseq = substitution_in_constraint_with_loc(seq, rep, name)
            return UninterpretedFunctionDeclaration(ufd_name, ufd_type, nseq)
        case ReflectedFunctionDeclaration(rfd_name, rfd_type, params, body, seq):
            nbody = substitution_in_liquid_with_loc(body, rep, name)
            nseq = substitution_in_constraint_with_loc(seq, rep, name)
            return ReflectedFunctionDeclaration(rfd_name, rfd_type, params, nbody, nseq)
        case _:
            assert False


# ---------------------------------------------------------------------------
# Term-for-term substitution (for non-variable equalities like size(x) == 3)
# ---------------------------------------------------------------------------


def substitute_liquid_term(t: LiquidTerm, old: LiquidTerm, new: LiquidTerm) -> LiquidTerm:
    """Replace every occurrence of *old* inside *t* with *new*.

    The replacement inherits the source location of the matched sub-expression
    so that error messages point to the right place.
    """
    if t == old:
        return with_location(new, t.loc)
    match t:
        case LiquidApp(fun, args, loc):
            return LiquidApp(fun, [substitute_liquid_term(a, old, new) for a in args], loc=loc)
        case _:
            return t


def substitute_liquid_term_in_constraint(c: Constraint, old: LiquidTerm, new: LiquidTerm) -> Constraint:
    """Replace every occurrence of liquid term *old* with *new* throughout a constraint."""
    match c:
        case LiquidConstraint(expr):
            return LiquidConstraint(substitute_liquid_term(expr, old, new), loc=c.loc)
        case Conjunction(c1, c2):
            return Conjunction(
                substitute_liquid_term_in_constraint(c1, old, new),
                substitute_liquid_term_in_constraint(c2, old, new),
                loc=c.loc,
            )
        case Implication(iname, base, pred, seq):
            return Implication(
                iname,
                base,
                substitute_liquid_term(pred, old, new),
                substitute_liquid_term_in_constraint(seq, old, new),
                loc=c.loc,
            )
        case UninterpretedFunctionDeclaration(uname, utype, seq):
            return UninterpretedFunctionDeclaration(uname, utype, substitute_liquid_term_in_constraint(seq, old, new))
        case ReflectedFunctionDeclaration(rname, rtype, params, body, seq):
            return ReflectedFunctionDeclaration(
                rname,
                rtype,
                params,
                substitute_liquid_term(body, old, new),
                substitute_liquid_term_in_constraint(seq, old, new),
            )
        case _:
            assert False


# ---------------------------------------------------------------------------
# Location propagation for binder elimination
# ---------------------------------------------------------------------------


def _propagate_loc(c: Constraint, loc: Location | None) -> Constraint:
    """When an ``Implication`` is eliminated by equality substitution, its
    source location (pointing to the call site / usage site) must not be lost.
    This helper transfers *loc* to the result constraint so that
    ``constraint_location`` still resolves to the right source position."""
    if loc is None:
        return c
    match c:
        case LiquidConstraint(expr, loc=existing):
            if existing is None:
                return LiquidConstraint(expr, loc=loc)
            return c
        case Implication(name, base, pred, seq, loc=existing):
            if existing is None:
                return Implication(name, base, pred, seq, loc=loc)
            return c
        case Conjunction(c1, c2, loc=existing):
            if existing is None:
                return Conjunction(c1, c2, loc=loc)
            return c
        case _:
            return c


# ---------------------------------------------------------------------------
# Equality extraction from conjunctive predicates
# ---------------------------------------------------------------------------


def _extract_var_equality(conjuncts: list[LiquidTerm], iname: Name) -> tuple[list[LiquidTerm], LiquidTerm] | None:
    """Find an equality conjunct that directly equates *iname* to some expression.

    Returns ``(remaining_conjuncts, replacement)`` on success, ``None`` if no
    such equality exists. Variable equalities are preferred because they
    completely eliminate the bound variable.
    """
    for i, conj in enumerate(conjuncts):
        if isinstance(conj, LiquidApp) and conj.fun == Name("==", 0) and len(conj.args) == 2:
            lhs, rhs = conj.args
            if lhs == LiquidVar(iname):
                return (conjuncts[:i] + conjuncts[i + 1 :], rhs)
            if rhs == LiquidVar(iname):
                return (conjuncts[:i] + conjuncts[i + 1 :], lhs)
    return None


def _extract_term_equality(
    conjuncts: list[LiquidTerm], iname: Name
) -> tuple[list[LiquidTerm], LiquidTerm, LiquidTerm] | None:
    """Find an equality conjunct of the form ``f(…iname…) == expr`` where only
    one side mentions *iname*.

    Returns ``(remaining_conjuncts, complex_side, simple_side)`` on success.
    """
    for i, conj in enumerate(conjuncts):
        if isinstance(conj, LiquidApp) and conj.fun == Name("==", 0) and len(conj.args) == 2:
            lhs, rhs = conj.args
            lhs_has = iname in liquid_free_vars(lhs)
            rhs_has = iname in liquid_free_vars(rhs)
            if lhs_has and not rhs_has:
                return (conjuncts[:i] + conjuncts[i + 1 :], lhs, rhs)
            if rhs_has and not lhs_has:
                return (conjuncts[:i] + conjuncts[i + 1 :], rhs, lhs)
    return None


# ---------------------------------------------------------------------------
# Constant folding helpers
# ---------------------------------------------------------------------------


def _fold_int_binary(op: str, a: int, b: int) -> LiquidTerm | None:
    """Evaluate a binary operation on two integer literals, if possible."""
    if op == "+":
        return LiquidLiteralInt(a + b)
    if op == "-":
        return LiquidLiteralInt(a - b)
    if op == "*":
        return LiquidLiteralInt(a * b)
    if op == "/" and b != 0:
        v = a // b if (a >= 0) == (b > 0) or a % b == 0 else -((-a) // b)
        return LiquidLiteralInt(v)
    if op == "%" and b != 0:
        v = a % b if (a >= 0) == (b > 0) or a % b == 0 else -((-a) % b)
        return LiquidLiteralInt(v)
    if op == ">":
        return LiquidLiteralBool(a > b)
    if op == ">=":
        return LiquidLiteralBool(a >= b)
    if op == "<":
        return LiquidLiteralBool(a < b)
    if op == "<=":
        return LiquidLiteralBool(a <= b)
    if op == "!=":
        return LiquidLiteralBool(a != b)
    return None


def _fold_float_binary(op: str, a: float, b: float) -> LiquidTerm | None:
    """Evaluate a binary operation on two float literals, if possible."""
    if op == "+":
        return LiquidLiteralFloat(a + b)
    if op == "-":
        return LiquidLiteralFloat(a - b)
    if op == "*":
        return LiquidLiteralFloat(a * b)
    if op == "/" and b != 0.0:
        return LiquidLiteralFloat(a / b)
    if op == ">":
        return LiquidLiteralBool(a > b)
    if op == ">=":
        return LiquidLiteralBool(a >= b)
    if op == "<":
        return LiquidLiteralBool(a < b)
    if op == "<=":
        return LiquidLiteralBool(a <= b)
    if op == "!=":
        return LiquidLiteralBool(a != b)
    return None


def simplify_expr(expr: LiquidTerm) -> LiquidTerm:
    """Simplifies a liquid term by reducing it.

    This is the main expression-level simplification entry point.  All
    expression-level rules (boolean algebra, constant folding, algebraic
    identities) live here so that ``simplify_constraint_fixpoint`` picks them
    up automatically.  To add a new rule, append a ``if …`` block before the
    final ``return LiquidApp(…)``.
    """
    match expr:
        case LiquidApp(fun=fun, args=args):
            sargs = [simplify_expr(e) for e in args]

            # --- Boolean algebra ------------------------------------------------
            if fun == Name("&&", 0):
                if sargs[0] == LiquidLiteralBool(False) or sargs[1] == LiquidLiteralBool(False):
                    return LiquidLiteralBool(False)
                if sargs[0] == LiquidLiteralBool(True):
                    return sargs[1]
                if sargs[1] == LiquidLiteralBool(True):
                    return sargs[0]
                if sargs[0] == sargs[1]:
                    return sargs[0]
            if fun == Name("||", 0):
                if sargs[0] == LiquidLiteralBool(True) or sargs[1] == LiquidLiteralBool(True):
                    return LiquidLiteralBool(True)
                if sargs[0] == LiquidLiteralBool(False):
                    return sargs[1]
                if sargs[1] == LiquidLiteralBool(False):
                    return sargs[0]
                if sargs[0] == sargs[1]:
                    return sargs[0]
            if fun == Name("!", 0) and len(sargs) == 1:
                if sargs[0] == LiquidLiteralBool(True):
                    return LiquidLiteralBool(False)
                if sargs[0] == LiquidLiteralBool(False):
                    return LiquidLiteralBool(True)
                match sargs[0]:
                    case LiquidApp(fun=f0, args=a0) if f0 == Name("!", 0) and len(a0) == 1:
                        return a0[0]
                    case _:
                        pass
            if fun == Name("==", 0) and len(sargs) == 2 and sargs[0] == sargs[1]:
                return LiquidLiteralBool(True)

            # --- Constant folding on literals -----------------------------------
            if len(sargs) == 2:
                match (sargs[0], sargs[1]):
                    case (LiquidLiteralInt(a), LiquidLiteralInt(b)):
                        folded = _fold_int_binary(fun.name, a, b)
                        if folded is not None:
                            return folded
                    case (LiquidLiteralFloat(a), LiquidLiteralFloat(b)):
                        folded = _fold_float_binary(fun.name, a, b)
                        if folded is not None:
                            return folded
                    case _:
                        pass

            # --- Algebraic identities -------------------------------------------
            if fun == Name("+", 0) and len(sargs) == 2:
                if sargs[0] == LiquidLiteralInt(0):
                    return sargs[1]
                if sargs[1] == LiquidLiteralInt(0):
                    return sargs[0]
                if sargs[0] == LiquidLiteralFloat(0.0):
                    return sargs[1]
                if sargs[1] == LiquidLiteralFloat(0.0):
                    return sargs[0]
            if fun == Name("-", 0) and len(sargs) == 2:
                if sargs[1] == LiquidLiteralInt(0):
                    return sargs[0]
                if sargs[1] == LiquidLiteralFloat(0.0):
                    return sargs[0]
                if sargs[0] == sargs[1]:
                    return LiquidLiteralInt(0)
            if fun == Name("*", 0) and len(sargs) == 2:
                if sargs[0] == LiquidLiteralInt(0) or sargs[1] == LiquidLiteralInt(0):
                    return LiquidLiteralInt(0)
                if sargs[0] == LiquidLiteralInt(1):
                    return sargs[1]
                if sargs[1] == LiquidLiteralInt(1):
                    return sargs[0]
                if sargs[0] == LiquidLiteralFloat(1.0):
                    return sargs[1]
                if sargs[1] == LiquidLiteralFloat(1.0):
                    return sargs[0]

            return LiquidApp(fun, sargs)
        case _:
            return expr


def constraint_free_variables(c: Constraint) -> list[Name]:
    """Returns all free variables in a constraint."""
    match c:
        case LiquidConstraint(expr=expr):
            return liquid_free_vars(expr)
        case UninterpretedFunctionDeclaration():
            return []
        case ReflectedFunctionDeclaration(body=body, params=params, seq=seq):
            return [v for v in liquid_free_vars(body) if v not in params] + constraint_free_variables(seq)
        case Implication(name=iname, pred=pred, seq=seq):
            lv = liquid_free_vars(pred)
            rv = constraint_free_variables(seq)
            return [x for x in lv + rv if x != iname]
        case Conjunction(c1=c1, c2=c2):
            return constraint_free_variables(c1) + constraint_free_variables(c2)
        case _:
            assert False, f"Unsupported Constraint: {c}"


def substitution_in_constraint(c: Constraint, rep: LiquidTerm, name: Name) -> Constraint:
    """Substitues a LiquidVar by another expression within a constraint."""
    match c:
        case LiquidConstraint(expr):
            return LiquidConstraint(substitution_in_liquid(expr, rep, name), loc=c.loc)
        case Conjunction(c1, c2):
            left = substitution_in_constraint(c1, rep, name)
            right = substitution_in_constraint(c2, rep, name)
            return Conjunction(left, right, loc=c.loc)
        case Implication(impl_name, base, pred, seq):
            if name == impl_name:
                return c
            else:
                nseq = substitution_in_constraint(seq, rep, name)
                return Implication(impl_name, base, substitution_in_liquid(pred, rep, name), nseq, loc=c.loc)
        case UninterpretedFunctionDeclaration(ufd_name, ufd_type, seq):
            nseq = substitution_in_constraint(seq, rep, name)
            return UninterpretedFunctionDeclaration(ufd_name, ufd_type, nseq)
        case ReflectedFunctionDeclaration(rfd_name, rfd_type, params, body, seq):
            nbody = substitution_in_liquid(body, rep, name)
            nseq = substitution_in_constraint(seq, rep, name)
            return ReflectedFunctionDeclaration(rfd_name, rfd_type, params, nbody, nseq)
        case _:
            assert False


def used_variables(c: LiquidTerm) -> set[Name]:
    """Returns all non-function variables used in an expression."""
    return {x for x in liquid_free_vars(c) if x.name not in base_functions}


def is_synthesized_name(name: Name) -> bool:
    """Returns True if the variable is a synthesized Form B existential binder.

    `synth(Application)` introduces `_y` binders for non-trivial arguments
    (replacing the old ANF `_anf` let-bindings). When such a binder only
    carries an equality refinement, `simplify_constraint` can substitute it
    away to keep the SMT query small.
    """
    return name.name == "_y"


def liquid_terms_alpha_equal(t1: LiquidTerm, t2: LiquidTerm) -> bool:
    """Checks if two liquid terms are alpha-equivalent (structurally equal ignoring name IDs)."""
    match (t1, t2):
        case (LiquidLiteralBool(b1), LiquidLiteralBool(b2)):
            return b1 == b2
        case (LiquidLiteralInt(i1), LiquidLiteralInt(i2)):
            return i1 == i2
        case (LiquidLiteralFloat(f1), LiquidLiteralFloat(f2)):
            return f1 == f2
        case (LiquidLiteralString(s1), LiquidLiteralString(s2)):
            return s1 == s2
        case (LiquidLiteralUnit(), LiquidLiteralUnit()):
            return True
        case (LiquidVar(n1), LiquidVar(n2)):
            return n1.name == n2.name and n1.id == n2.id
        case (LiquidApp(fun1, args1), LiquidApp(fun2, args2)):
            if fun1.name != fun2.name or len(args1) != len(args2):
                return False
            return all(liquid_terms_alpha_equal(a1, a2) for a1, a2 in zip(args1, args2))
        case _:
            return False


def simplify_implication_conclusion(pred: LiquidTerm, conclusion: LiquidTerm) -> LiquidTerm:
    """Simplifies the conclusion of an implication by removing conjuncts that are already in the premise.

    Example: premise: a > 0, conclusion: a > 0 && b > 0 => simplified to: b > 0
    """
    premise_conjuncts = flatten_conjuncts(pred)
    conclusion_conjuncts = flatten_conjuncts(conclusion)

    # Remove conclusion conjuncts that are already present in the premise
    simplified_conjuncts = [
        conc
        for conc in conclusion_conjuncts
        if not any(liquid_terms_alpha_equal(conc, prem) for prem in premise_conjuncts)
    ]

    return rebuild_conjunction(simplified_conjuncts)


def simplify_constraint(c: Constraint) -> Constraint:
    """Converts a constraint into an equivalent one, by reducing it to
    equivalent expressions.

    This is the main constraint-level simplification entry point.  All
    constraint-level rules (equality elimination, binder dropping, conclusion
    simplification) live here so that ``simplify_constraint_fixpoint`` picks
    them up automatically.  To add a new rule, add a new ``case`` or ``if``
    block in the ``Implication`` arm.
    """
    match c:
        case LiquidConstraint(expr=expr):
            return LiquidConstraint(simplify_expr(expr), loc=c.loc)
        case Conjunction(c1=c1, c2=c2):
            left = simplify_constraint(c1)
            right = simplify_constraint(c2)
            if left == right:
                return left
            if isinstance(left, LiquidConstraint) and left.expr == LiquidLiteralBool(False):
                return left
            if isinstance(right, LiquidConstraint) and right.expr == LiquidLiteralBool(False):
                return right
            if isinstance(left, LiquidConstraint) and left.expr == LiquidLiteralBool(True):
                return right
            if isinstance(right, LiquidConstraint) and right.expr == LiquidLiteralBool(True):
                return left
            return Conjunction(left, right)
        case Implication(name=iname, base=base, pred=pred, seq=seq, loc=iloc):
            if pred == LiquidLiteralBool(True) and seq == LiquidConstraint(LiquidLiteralBool(True)):
                return seq

            # --- Equality elimination (variable) --------------------------------
            # If the predicate (or any conjunct of it) equates the bound
            # variable to an expression, substitute the variable away.  This
            # generalises the old ``_y``-only rule to *all* bound variables.
            conjuncts = flatten_conjuncts(pred)
            var_eq = _extract_var_equality(conjuncts, iname)
            if var_eq is not None:
                remaining, rep = var_eq
                subs_remaining = [substitution_in_liquid_with_loc(c, rep, iname) for c in remaining]
                subs_seq = substitution_in_constraint_with_loc(seq, rep, iname)
                if not subs_remaining:
                    return _propagate_loc(simplify_constraint(subs_seq), iloc)
                new_pred = simplify_expr(rebuild_conjunction(subs_remaining))
                return simplify_constraint(
                    Implication(Name("_", fresh_counter.fresh()), t_bool, new_pred, subs_seq, loc=iloc)
                )

            # --- Equality elimination (non-variable / function application) ------
            # Handles cases like ``forall x:K, size(x) == 3 -> size(x) > 0``
            # by substituting the complex side with the simple side.
            term_eq = _extract_term_equality(conjuncts, iname)
            if term_eq is not None:
                remaining, complex_side, simple_side = term_eq
                subs_remaining = [substitute_liquid_term(c, complex_side, simple_side) for c in remaining]
                subs_seq = substitute_liquid_term_in_constraint(seq, complex_side, simple_side)
                new_pred = simplify_expr(rebuild_conjunction(subs_remaining))
                all_free = liquid_free_vars(new_pred)
                seq_uses = is_used(iname, subs_seq)
                if iname not in all_free and not seq_uses:
                    if not subs_remaining:
                        return _propagate_loc(simplify_constraint(subs_seq), iloc)
                    return simplify_constraint(
                        Implication(Name("_", fresh_counter.fresh()), t_bool, new_pred, subs_seq, loc=iloc)
                    )
                return simplify_constraint(Implication(iname, base, new_pred, subs_seq, loc=iloc))

            cont = simplify_constraint(seq)
            s = simplify_expr(pred)

            iname_used_in_original = is_used(iname, cont)

            if isinstance(cont, LiquidConstraint):
                simplified_conclusion = simplify_implication_conclusion(s, cont.expr)
                if simplified_conclusion != cont.expr:
                    cont = LiquidConstraint(simplify_expr(simplified_conclusion), loc=cont.loc)

            other_used_vars = [x for x in used_variables(s) if x != iname]
            if not iname_used_in_original and not other_used_vars:
                return cont

            return Implication(iname, base, s, cont, loc=iloc)
        case UninterpretedFunctionDeclaration(name=uname, type=utype, seq=useq):
            cont = simplify_constraint(useq)
            return UninterpretedFunctionDeclaration(uname, utype, cont)
        case ReflectedFunctionDeclaration(name=rname, type=rtype, params=rparams, body=rbody, seq=rseq):
            cont = simplify_constraint(rseq)
            return ReflectedFunctionDeclaration(rname, rtype, rparams, simplify_expr(rbody), cont)
        case _:
            return c


def simplify_constraint_fixpoint(
    c: Constraint,
    max_steps: int = 32,
    extra_passes: list[Callable[[Constraint], Constraint]] | None = None,
) -> Constraint:
    """Apply all simplification passes in a loop until the constraint stabilises.

    Each iteration runs ``simplify_constraint`` (which internally calls
    ``simplify_expr`` for expression-level rules such as constant folding and
    boolean algebra) followed by any caller-supplied *extra_passes*.

    To extend the fixpoint with a new rewrite rule you can either:

    * Add expression-level rules to ``simplify_expr``.
    * Add constraint-level rules to ``simplify_constraint``.
    * Pass one-off passes via *extra_passes*.
    """
    passes: list[Callable[[Constraint], Constraint]] = [simplify_constraint]
    if extra_passes:
        passes.extend(extra_passes)

    cur = c
    for _ in range(max_steps):
        nxt = cur
        for p in passes:
            nxt = p(nxt)
        if nxt == cur:
            return cur
        cur = nxt
    return cur


def conjunctive_normal_form(c: Constraint) -> Generator[Constraint, None, None]:
    """Converts a constraint to its conjunctive normal form."""
    match c:
        case LiquidConstraint():
            yield c
        case Conjunction(c1=c1, c2=c2):
            yield from conjunctive_normal_form(c1)
            yield from conjunctive_normal_form(c2)
        case Implication(name=iname, base=base, pred=pred, seq=seq, loc=iloc):
            for inner in conjunctive_normal_form(seq):
                yield Implication(iname, base, pred, inner, loc=iloc)
        case UninterpretedFunctionDeclaration(name=uname, type=utype, seq=useq):
            for inner in conjunctive_normal_form(useq):
                yield UninterpretedFunctionDeclaration(uname, utype, inner)
        case ReflectedFunctionDeclaration(name=rname, type=rtype, params=rparams, body=rbody, seq=rseq):
            for inner in conjunctive_normal_form(rseq):
                yield ReflectedFunctionDeclaration(rname, rtype, rparams, rbody, inner)
        case _:
            assert False


def split_or_disjuncts(expr: LiquidTerm) -> list[LiquidConstraint]:
    """Flattens OR in the conclusion into a list of disjuncts."""
    match expr:
        case LiquidApp(fun=f, args=[a0, a1]) if f == Name("||", 0):
            return split_or_disjuncts(a0) + split_or_disjuncts(a1)
        case _:
            return [LiquidConstraint(expr)]


def split_or_in_conclusion(c: Constraint) -> list[Constraint]:
    """Splits OR in the conclusion (innermost LiquidConstraint) into separate VCs."""
    match c:
        case LiquidConstraint(expr=expr):
            return cast(list[Constraint], split_or_disjuncts(expr))
        case Implication(name=iname, base=base, pred=pred, seq=seq, loc=iloc):
            return [Implication(iname, base, pred, s, loc=iloc) for s in split_or_in_conclusion(seq)]
        case UninterpretedFunctionDeclaration(name=uname, type=utype, seq=useq):
            return [UninterpretedFunctionDeclaration(uname, utype, s) for s in split_or_in_conclusion(useq)]
        case ReflectedFunctionDeclaration(name=rname, type=rtype, params=rparams, body=rbody, seq=rseq):
            return [ReflectedFunctionDeclaration(rname, rtype, rparams, rbody, s) for s in split_or_in_conclusion(rseq)]
        case _:
            return [c]


def split_and_conjuncts(expr: LiquidTerm) -> list[LiquidTerm]:
    """Flattens AND in the conclusion into a list of conjuncts."""
    conjuncts = flatten_conjuncts(expr)
    return conjuncts if conjuncts else [expr]


def split_and_in_conclusion(c: Constraint) -> list[Constraint]:
    """Splits AND in the conclusion (innermost LiquidConstraint) into separate VCs."""
    match c:
        case LiquidConstraint(expr=expr, loc=loc):
            conjuncts = split_and_conjuncts(expr)
            if len(conjuncts) <= 1:
                return [c]
            return [LiquidConstraint(conj, loc=loc) for conj in conjuncts]
        case Implication(name=iname, base=base, pred=pred, seq=seq, loc=iloc):
            return [Implication(iname, base, pred, s, loc=iloc) for s in split_and_in_conclusion(seq)]
        case UninterpretedFunctionDeclaration(name=uname, type=utype, seq=useq):
            return [UninterpretedFunctionDeclaration(uname, utype, s) for s in split_and_in_conclusion(useq)]
        case ReflectedFunctionDeclaration(name=rname, type=rtype, params=rparams, body=rbody, seq=rseq):
            return [
                ReflectedFunctionDeclaration(rname, rtype, rparams, rbody, s) for s in split_and_in_conclusion(rseq)
            ]
        case _:
            return [c]


def is_false_liquid(expr: LiquidTerm) -> bool:
    """Returns whether a liquid term simplifies to ``false``."""
    return simplify_expr(expr) == LiquidLiteralBool(False)


def conclusion_variables(c: Constraint) -> set[Name]:
    """Returns free variables appearing in the innermost conclusion."""
    match c:
        case LiquidConstraint(expr=expr):
            return used_variables(expr)
        case Implication(seq=seq):
            return conclusion_variables(seq)
        case UninterpretedFunctionDeclaration(seq=seq):
            return conclusion_variables(seq)
        case ReflectedFunctionDeclaration(seq=seq):
            return conclusion_variables(seq)
        case Conjunction(c1=c1, c2=c2):
            return conclusion_variables(c1).union(conclusion_variables(c2))
        case _:
            return set()


def _extract_var_literal_bound(
    expr: LiquidTerm,
) -> tuple[Name, str, int] | None:
    """If *expr* is ``var op literal`` or ``literal op var``, return ``(var, op, n)``."""
    match expr:
        case LiquidApp(fun=f, args=[LiquidVar(name), LiquidLiteralInt(n)]) if f.name in {">", ">=", "<", "<="}:
            return (name, f.name, n)
        case LiquidApp(fun=f, args=[LiquidLiteralInt(n), LiquidVar(name)]) if f.name in {">", ">=", "<", "<="}:
            op = f.name
            if op == ">":
                op = "<"
            elif op == ">=":
                op = "<="
            elif op == "<":
                op = ">"
            elif op == "<=":
                op = ">="
            return (name, op, n)
        case _:
            return None


def _bounds_contradict(left: tuple[Name, str, int], right: tuple[Name, str, int]) -> bool:
    """Detect incompatible literal bounds on the same variable."""
    (v1, op1, n1), (v2, op2, n2) = left, right
    if v1.name != v2.name or v1.id != v2.id:
        return False

    def lower_bound(op: str, n: int) -> tuple[bool, int] | None:
        if op in {">", ">="}:
            return (op == ">", n)
        if op in {"<", "<="}:
            return (op == "<", n)
        return None

    lb = lower_bound(op1, n1)
    rb = lower_bound(op2, n2)
    if lb is None or rb is None:
        return False

    (strict_l, lo), (strict_u, hi) = lb, rb
    if strict_l and strict_u:
        return lo >= hi
    if strict_l and not strict_u:
        return lo >= hi
    if not strict_l and strict_u:
        return lo > hi
    return lo > hi


def _extract_var_equality_value(expr: LiquidTerm) -> tuple[Name, LiquidTerm] | None:
    match expr:
        case LiquidApp(fun=f, args=[LiquidVar(name), rhs]) if f == Name("==", 0):
            return (name, rhs)
        case LiquidApp(fun=f, args=[lhs, LiquidVar(name)]) if f == Name("==", 0):
            return (name, lhs)
        case _:
            return None


def _equalities_contradict(a: LiquidTerm, b: LiquidTerm) -> bool:
    eq_a = _extract_var_equality_value(a)
    eq_b = _extract_var_equality_value(b)
    if eq_a is None or eq_b is None:
        return False
    (v1, rhs1), (v2, rhs2) = eq_a, eq_b
    if v1.name != v2.name or v1.id != v2.id:
        return False
    return not liquid_terms_alpha_equal(rhs1, rhs2)


def predicates_contradict(p1: LiquidTerm, p2: LiquidTerm) -> bool:
    """Conservative syntactic check for contradictory preconditions."""
    for c1 in flatten_conjuncts(p1) or [p1]:
        for c2 in flatten_conjuncts(p2) or [p2]:
            if _equalities_contradict(c1, c2):
                return True
            b1 = _extract_var_literal_bound(c1)
            b2 = _extract_var_literal_bound(c2)
            if b1 is not None and b2 is not None and _bounds_contradict(b1, b2):
                return True
    return False


def _should_keep_precondition(
    iname: Name,
    pred: LiquidTerm,
    goal_vars: set[Name],
    other_preds: list[LiquidTerm],
) -> bool:
    """Keep preconditions that are false, contradictory, or mention goal variables."""
    if is_false_liquid(pred):
        return True
    if any(predicates_contradict(pred, other) for other in other_preds):
        return True
    pred_vars = used_variables(pred)
    pred_vars.add(iname)
    return not goal_vars.isdisjoint(pred_vars)


def remove_inert_preconditions(c: Constraint) -> Constraint:
    """Drop implication preconditions that do not affect the displayed goal."""
    match c:
        case UninterpretedFunctionDeclaration(name=uname, type=utype, seq=useq):
            return UninterpretedFunctionDeclaration(uname, utype, remove_inert_preconditions(useq))
        case ReflectedFunctionDeclaration(name=rname, type=rtype, params=rparams, body=rbody, seq=rseq):
            return ReflectedFunctionDeclaration(rname, rtype, rparams, rbody, remove_inert_preconditions(rseq))
        case _:
            return _remove_inert_implication_chain(c)


def _remove_inert_implication_chain(c: Constraint) -> Constraint:
    parts: list[tuple[Name, TypeConstructor | TypeVar | Top, LiquidTerm, Location | None]] = []
    goal = c
    while isinstance(goal, Implication):
        parts.append((goal.name, goal.base, goal.pred, goal.loc))
        goal = goal.seq

    goal_vars = conclusion_variables(goal)
    kept: list[tuple[Name, TypeConstructor | TypeVar | Top, LiquidTerm, Location | None]] = []
    for i, (iname, base, pred, loc) in enumerate(parts):
        others = [p for j, (_, _, p, _) in enumerate(parts) if j != i]
        if _should_keep_precondition(iname, pred, goal_vars, others):
            kept.append((iname, base, pred, loc))

    result = goal
    for iname, base, pred, loc in reversed(kept):
        result = Implication(iname, base, pred, result, loc=loc)
    return result


def prepare_vc_for_display(c: Constraint) -> Constraint:
    """Simplify a VC for error messages: rewrite, drop inert preconditions, prune context."""
    cons_simp = simplify_constraint_fixpoint(c)
    cons_clean = remove_inert_preconditions(cons_simp)
    cons_clean, _ = remove_unrelated_context(cons_clean, ignore_vars=set())
    return cons_clean


def render_constraint_for_display(c: Constraint) -> str:
    """Render a constraint as (multi-line) text *without* simplifying it.

    Unlike :func:`pretty_print_constraint` this does not run
    :func:`prepare_vc_for_display` first, so it can show a specific intermediate
    form of a VC verbatim (used by :func:`vc_simplification_steps`). Conjunctions
    are still split via CNF and trivial ``… -> true`` parts dropped, and each
    conjunct is indented with two spaces per level so it reads well in a plain
    ``<pre>`` block."""
    parts: list[str] = []
    for cons in conjunctive_normal_form(c):
        if is_implication_true(cons):
            continue
        lines = [indent * "  " + item for item, indent in pretty_print_generator(cons)]
        parts.append("\n".join(lines))
    if not parts:
        return "true"
    return "\n\n".join(parts)


def vc_simplification_steps(c: Constraint, max_steps: int = 32) -> list[tuple[str, str]]:
    """The labelled progression of a VC from its original form to the fully
    simplified form shown in error messages.

    Returns a list of ``(label, rendered_text)`` pairs ordered original →
    simplified; the final element is exactly what :func:`prepare_vc_for_display`
    produces. This mirrors :func:`prepare_vc_for_display` step by step —
    per-iteration constraint rewriting, then inert-precondition removal, then
    unrelated-context pruning — so an editor can present the simplified VC and
    let the user expand back through each simplification step to the version
    that preceded it. Steps whose rendered text is identical to the previous
    one are collapsed (the later, more descriptive label is kept)."""
    stages: list[tuple[str, Constraint]] = [("Original", c)]

    cur = c
    for i in range(max_steps):
        nxt = simplify_constraint(cur)
        if nxt == cur:
            break
        cur = nxt
        stages.append((f"Rewrite pass {i + 1}", cur))

    cons_clean = remove_inert_preconditions(cur)
    stages.append(("Drop inert preconditions", cons_clean))

    cons_pruned, _ = remove_unrelated_context(cons_clean, ignore_vars=set())
    stages.append(("Prune unrelated context", cons_pruned))

    out: list[tuple[str, str]] = []
    for label, cons in stages:
        try:
            text = render_constraint_for_display(cons)
        except Exception:
            continue
        # Collapse steps that render identically, keeping the earlier (more
        # faithful) label; the final entry still carries the fully simplified
        # text that ``prepare_vc_for_display`` produces.
        if out and out[-1][1] == text:
            continue
        out.append((label, text))
    return out


def pretty_print_generator(c: Constraint) -> Generator[tuple[str, int], None, None]:
    """Recursive generates a list of items to print, with the respective
    indentation level."""
    match c:
        case LiquidConstraint(expr=expr):
            yield (f"{expr}", 0)
        case UninterpretedFunctionDeclaration(name=uname, type=utype, seq=useq):
            yield (f"fun {uname} : {utype}", 0)
            yield from pretty_print_generator(useq)
        case ReflectedFunctionDeclaration(name=rname, type=rtype, params=rparams, seq=rseq):
            params = ", ".join(str(p) for p in rparams)
            yield (f"reflected {rname}({params}) : {rtype}", 0)
            yield from pretty_print_generator(rseq)
        case Implication(name=iname, base=base, pred=pred, seq=sseq):
            trivial_pred = pred == LiquidLiteralBool(True)
            if is_used(iname, sseq):
                if trivial_pred:
                    yield (f"∀{iname}:{base}", 0)
                else:
                    yield (f"∀{iname}:{base} | {pred}", 0)
            else:
                if not trivial_pred:
                    yield (f"{iname}:_ | {pred}", 0)
            if not isinstance(sseq, Implication):
                yield ("====>", 0)
            yield from pretty_print_generator(sseq)
        case Conjunction():
            assert False
        case _:
            assert False


def is_implication_true(c: Constraint):
    """Returns whether a given constraint has the shape ...

    -> true
    """
    match c:
        case LiquidConstraint(expr=expr):
            return expr == LiquidLiteralBool(True)
        case UninterpretedFunctionDeclaration(seq=seq):
            return is_implication_true(seq)
        case ReflectedFunctionDeclaration(seq=seq):
            return is_implication_true(seq)
        case Implication(seq=seq):
            return is_implication_true(seq)
        case Conjunction(c1=c1, c2=c2):
            return is_implication_true(c1) and is_implication_true(c2)
        case _:
            assert False


def remove_unrelated_context(c: Constraint, ignore_vars: set[Name]) -> tuple[Constraint, set[Name]]:
    """Removes variables and conditions that are unrelated to the goal."""
    match c:
        case LiquidConstraint(expr=expr):
            return (c, used_variables(expr).difference(ignore_vars or []))
        case UninterpretedFunctionDeclaration(name=uname, seq=useq):
            return remove_unrelated_context(useq, ignore_vars.union([uname]))
        case ReflectedFunctionDeclaration(name=rname, seq=rseq):
            return remove_unrelated_context(rseq, ignore_vars.union([rname]))
        case Implication(name=iname, pred=pred, seq=seq):
            (ic, vs) = remove_unrelated_context(seq, ignore_vars)
            current_vars = used_variables(pred).difference(ignore_vars)
            current_vars.add(iname)
            if vs.isdisjoint(current_vars):
                return (ic, vs)
            return (c, vs.union(current_vars).difference({iname}))
        case Conjunction(c1=c1, c2=c2, loc=cloc):
            (p1, vs1) = remove_unrelated_context(c1, ignore_vars)
            (p2, vs2) = remove_unrelated_context(c2, ignore_vars)
            return (Conjunction(p1, p2, loc=cloc), vs1.union(vs2))
        case _:
            assert False


def reduce_to_useful_constraint(c: Constraint) -> Constraint:
    top = []
    for cons in conjunctive_normal_form(c):
        if not is_implication_true(cons):
            top.append(prepare_vc_for_display(cons))
    llb = LiquidLiteralBool(True)
    return reduce(Conjunction, top, LiquidConstraint(llb))  # type: ignore


def pretty_print_constraint(c: Constraint) -> str:
    """Returns a string representation of a given Constraint.

    To help in reading the constraint, the following optimizations are performed:
    * Conjunctions are expanded into Conjunctive Normal Form.
    * Constrains in the form "sth -> true" are ommited.
    * Constraints are simplified, removing unused variables with no conditions.
    * Constraints are simplified, by removing variables that are not used inside.
    """

    top = []
    for cons in conjunctive_normal_form(c):
        if not is_implication_true(cons):
            r = []
            cons_clean = prepare_vc_for_display(cons)
            for item, indent in pretty_print_generator(cons_clean):
                r.append(indent * "\t" + item)
            top.append("\n".join(r))
    header = "\n+-----Constraint-----+\n"
    middle = "\n+--------------------+\n".join(top)
    footer = "\n+---------//---------+\n"
    return header + middle + footer


def constraint_goal(c: Constraint) -> LiquidTerm | None:
    """Return the goal (innermost conclusion) of a constraint.

    A verification condition has the shape ``∀…, premises => goal``; this digs
    through the binders/premises to the final ``LiquidConstraint`` and returns
    its expression, which is the property that actually has to hold. Used to
    surface the concrete goal at the top of an error message.
    """
    match c:
        case LiquidConstraint(expr=expr):
            return expr
        case Implication(seq=seq):
            return constraint_goal(seq)
        case UninterpretedFunctionDeclaration(seq=seq):
            return constraint_goal(seq)
        case ReflectedFunctionDeclaration(seq=seq):
            return constraint_goal(seq)
        case _:
            return None


def show_constraint(c: Constraint):
    print("Could not show constrain:")
    print(pretty_print_constraint(c))
