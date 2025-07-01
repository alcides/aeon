from __future__ import annotations

from functools import reduce
from typing import Generator

from aeon.core.liquid import liquid_free_vars
from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import liquefy
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType, TypeConstructor, Top, TypeVar
from aeon.core.types import t_bool
from aeon.frontend.parser import parse_term
from aeon.verification.smt import base_functions
from aeon.verification.vcs import Conjunction
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import Implication
from aeon.verification.vcs import LiquidConstraint
from aeon.verification.vcs import UninterpretedFunctionDeclaration
from aeon.utils.name import Name, fresh_counter


def parse_liquid(t: str) -> LiquidTerm | None:
    tp = parse_term(t)
    tl = liquefy(tp)
    return tl


def imp(a: str | LiquidTerm, b: Constraint) -> Constraint:
    e = a if isinstance(a, LiquidTerm) else parse_liquid(a)
    assert e is not None
    return Implication(Name("_", fresh_counter.fresh()), t_bool, e, b)


def conj(a: Constraint, b: Constraint) -> Constraint:
    return Conjunction(a, b)


def end(a: str | LiquidTerm) -> LiquidConstraint:
    e = a if isinstance(a, LiquidTerm) else parse_liquid(a)
    assert e is not None
    return LiquidConstraint(e)


def constraint_builder(vs: list[tuple[Name, TypeConstructor | TypeVar | AbstractionType | Top]], exp: Constraint):
    for n, t in vs[::-1]:
        if isinstance(t, AbstractionType):
            exp = UninterpretedFunctionDeclaration(n, t, exp)
        else:
            exp = Implication(n, t, LiquidLiteralBool(True), exp)
    return exp


def simplify_is_true(c: Constraint):
    return isinstance(c, LiquidConstraint) and c.expr == LiquidLiteralBool(True)


def is_whitespace(s: str) -> bool:
    return all(x in ["\t\n "] for x in s)


def flatten_conjunctions(c: Conjunction) -> list[Constraint]:
    queue = [c.c1, c.c2]
    conjunctions = []

    while queue:
        o = queue.pop()
        if isinstance(o, Conjunction):
            queue.append(o.c1)
            queue.append(o.c2)
        elif simplify_is_true(o):
            pass
        else:
            conjunctions.append(o)
    return conjunctions


def is_used_liquid(n: Name, c: LiquidTerm) -> bool:
    return n in liquid_free_vars(c)


def is_used(n: Name, c: Constraint) -> bool:
    if isinstance(c, LiquidConstraint):
        return is_used_liquid(n, c.expr)
    elif isinstance(c, UninterpretedFunctionDeclaration):
        return False
    elif isinstance(c, Implication):
        if n == c.name:
            return False
        return is_used_liquid(n, c.pred) or is_used(n, c.seq)
    elif isinstance(c, Conjunction):
        return is_used(n, c.c1) or is_used(n, c.c2)
    else:
        assert False, f"Unsupported Constraint: {c}"


def simplify_expr(expr: LiquidTerm) -> LiquidTerm:
    """Simplifies a liquid term by reducing it."""
    if isinstance(expr, LiquidApp) and expr.fun == Name("&&", 0):
        if expr.args[0] == LiquidLiteralBool(True):
            return simplify_expr(expr.args[1])
        elif expr.args[1] == LiquidLiteralBool(True):
            return simplify_expr(expr.args[0])
    if isinstance(expr, LiquidApp) and expr.fun == Name("||", 0):
        if expr.args[0] == LiquidLiteralBool(False):
            return simplify_expr(expr.args[1])
        elif expr.args[1] == LiquidLiteralBool(False):
            return simplify_expr(expr.args[0])
    if isinstance(expr, LiquidApp):
        return LiquidApp(expr.fun, [simplify_expr(e) for e in expr.args])
    return expr


def constraint_free_variables(c: Constraint) -> list[Name]:
    """Returns all free variables in a constraint."""
    if isinstance(c, LiquidConstraint):
        return liquid_free_vars(c.expr)
    elif isinstance(c, UninterpretedFunctionDeclaration):
        return []
    elif isinstance(c, Implication):
        lv = liquid_free_vars(c.pred)
        rv = constraint_free_variables(c.seq)
        return [x for x in lv + rv if x != c.name]
    elif isinstance(c, Conjunction):
        return constraint_free_variables(c.c1) + constraint_free_variables(c.c2)
    else:
        assert False, f"Unsupported Constraint: {c}"


def substitution_in_constraint(c: Constraint, rep: LiquidTerm, name: Name) -> Constraint:
    """Substitues a LiquidVar by another expression within a constraint."""
    match c:
        case LiquidConstraint(expr):
            return LiquidConstraint(substitution_in_liquid(expr, rep, name))
        case Conjunction(c1, c2):
            left = substitution_in_constraint(c1, rep, name)
            right = substitution_in_constraint(c2, rep, name)
            return Conjunction(left, right)
        case Implication(name, base, pred, seq):
            if c.name == name:
                return c
            else:
                nseq = substitution_in_constraint(seq, rep, name)
                return Implication(name, base, substitution_in_liquid(pred, rep, name), nseq)
        case UninterpretedFunctionDeclaration(name, type, seq):
            nseq = substitution_in_constraint(seq, rep, name)
            return UninterpretedFunctionDeclaration(name, type, nseq)
        case _:
            assert False


def used_variables(c: LiquidTerm) -> set[Name]:
    """Returns all non-function variables used in an expression."""
    return {x for x in liquid_free_vars(c) if x.name not in base_functions}


def simplify_constraint(c: Constraint) -> Constraint:
    """Converts a constraint into an equivalent one, by reducing it to
    equivalent expressions."""
    if isinstance(c, LiquidConstraint):
        return LiquidConstraint(simplify_expr(c.expr))
    elif isinstance(c, Conjunction):
        left = simplify_constraint(c.c1)
        right = simplify_constraint(c.c2)
        if isinstance(left, LiquidConstraint) and left.expr == LiquidLiteralBool(True):
            return right
        elif isinstance(right, LiquidConstraint) and right.expr == LiquidLiteralBool(True):
            return left
        else:
            return Conjunction(left, right)
    elif isinstance(c, Implication):
        if c.pred == LiquidLiteralBool(True) and c.seq == LiquidConstraint(LiquidLiteralBool(True)):
            return c.seq

        # Preds are usually built as in (cond) && ( this = other)
        if (
            isinstance(c.pred, LiquidApp)
            and c.pred.fun == Name("&&", 0)
            and isinstance(c.pred.args[1], LiquidApp)
            and c.pred.args[1].fun == Name("==", 0)
            and c.pred.args[1].args[0] == LiquidVar(c.name)
        ):
            rep = c.pred.args[1].args[1]
            subs_pred = substitution_in_liquid(c.pred.args[0], rep, c.name)
            subs_seq = substitution_in_constraint(c.seq, rep, c.name)
            rc = simplify_constraint(Implication(Name("_", fresh_counter.fresh()), t_bool, subs_pred, subs_seq))
            return rc

        cont = simplify_constraint(c.seq)
        s = simplify_expr(c.pred)

        other_used_vars = [x for x in used_variables(s) if x != c.name]
        if not is_used(c.name, cont) and not other_used_vars:
            return c.seq

        return Implication(c.name, c.base, s, cont)
    elif isinstance(c, UninterpretedFunctionDeclaration):
        cont = simplify_constraint(c.seq)
        return UninterpretedFunctionDeclaration(c.name, c.type, cont)
    return c


def conjunctive_normal_form(c: Constraint) -> Generator[Constraint, None, None]:
    """Converts a constraint to its conjunctive normal form."""
    if isinstance(c, LiquidConstraint):
        yield c
    elif isinstance(c, Conjunction):
        yield from conjunctive_normal_form(c.c1)
        yield from conjunctive_normal_form(c.c2)
    elif isinstance(c, Implication):
        for inner in conjunctive_normal_form(c.seq):
            yield Implication(c.name, c.base, c.pred, inner)

    elif isinstance(c, UninterpretedFunctionDeclaration):
        for inner in conjunctive_normal_form(c.seq):
            yield UninterpretedFunctionDeclaration(c.name, c.type, inner)
    else:
        assert False


def pretty_print_generator(c: Constraint) -> Generator[tuple[str, int], None, None]:
    """Recursive generates a list of items to print, with the respective
    indentation level."""
    if isinstance(c, LiquidConstraint):
        yield (f"{c.expr}", 0)
    elif isinstance(c, UninterpretedFunctionDeclaration):
        yield (f"fun {c.name} : {c.type}", 0)
        yield from pretty_print_generator(c.seq)
    elif isinstance(c, Implication):
        if is_used(c.name, c.seq):
            yield (f"∀{c.name}:{c.base} | {c.pred}", 0)
        else:
            if c.pred != LiquidLiteralBool(True):
                yield (f"{c.name}:_ | {c.pred}", 0)
        if not isinstance(c.seq, Implication):
            yield ("====>", 0)
        yield from pretty_print_generator(c.seq)
    elif isinstance(c, Conjunction):
        assert False
    else:
        assert False


def is_implication_true(c: Constraint):
    """Returns whether a given constraint has the shape ...

    -> true
    """
    if isinstance(c, LiquidConstraint):
        return c.expr == LiquidLiteralBool(True)
    elif isinstance(c, UninterpretedFunctionDeclaration):
        return is_implication_true(c.seq)
    elif isinstance(c, Implication):
        return is_implication_true(c.seq)
    elif isinstance(c, Conjunction):
        return is_implication_true(c.c1) and is_implication_true(c.c2)
    else:
        assert False


def remove_unrelated_context(c: Constraint, ignore_vars: set[Name]) -> tuple[Constraint, set[Name]]:
    """Removes variables and conditions that are unrelated to the goal."""
    if isinstance(c, LiquidConstraint):
        return (c, used_variables(c.expr).difference(ignore_vars or []))
    elif isinstance(c, UninterpretedFunctionDeclaration):
        return remove_unrelated_context(c.seq, ignore_vars.union([c.name]))
    elif isinstance(c, Implication):
        (ic, vs) = remove_unrelated_context(c.seq, ignore_vars)
        current_vars = used_variables(c.pred).difference(ignore_vars)
        current_vars.add(c.name)
        if vs.isdisjoint(current_vars):
            return (ic, vs)
        else:
            return (c, vs.union(current_vars).difference({c.name}))
    elif isinstance(c, Conjunction):
        (p1, vs1) = remove_unrelated_context(c.c1, ignore_vars)
        (p2, vs2) = remove_unrelated_context(c.c2, ignore_vars)
        return (c, vs1.union(vs2))
    else:
        assert False


def reduce_to_useful_constraint(c: Constraint) -> Constraint:
    top = []
    for cons in conjunctive_normal_form(c):
        if not is_implication_true(cons):
            cons_simp = simplify_constraint(cons)
            cons_clean, _ = remove_unrelated_context(cons_simp, ignore_vars=set())
            top.append(cons_clean)
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
            cons_simp = simplify_constraint(cons)
            cons_clean, _ = remove_unrelated_context(cons_simp, ignore_vars=set())
            for item, indent in pretty_print_generator(cons_clean):
                r.append(indent * "\t" + item)
            top.append("\n".join(r))
    header = "\n+-----Constraint-----+\n"
    middle = "\n+--------------------+\n".join(top)
    footer = "\n+---------//---------+\n"
    return header + middle + footer


def show_constraint(c: Constraint):
    print("Could not show constrain:")
    print(pretty_print_constraint(c))
