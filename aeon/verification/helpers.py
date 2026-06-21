from __future__ import annotations

from functools import reduce
from typing import Generator, cast

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
from aeon.verification.vcs import substitution_in_constraint
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


def is_whitespace(s: str) -> bool:
    return all(x in ["\t\n "] for x in s)


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


def simplify_expr(expr: LiquidTerm) -> LiquidTerm:
    """Simplifies a liquid term by reducing it."""
    match expr:
        case LiquidApp(fun=fun, args=args):
            sargs = [simplify_expr(e) for e in args]
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
    equivalent expressions."""
    match c:
        case LiquidConstraint(expr=expr):
            return LiquidConstraint(simplify_expr(expr))
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

            # Remove synthesized existential binders that only have equality: forall v: v == expr => seq
            if is_synthesized_name(iname) and isinstance(pred, LiquidApp) and pred.fun == Name("==", 0):
                if pred.args[0] == LiquidVar(iname):
                    rep = pred.args[1]
                elif pred.args[1] == LiquidVar(iname):
                    rep = pred.args[0]
                else:
                    rep = None
                if rep is not None:
                    subs_seq = substitution_in_constraint(seq, rep, iname)
                    return simplify_constraint(subs_seq)

            # Preds are usually built as in (cond) && ( this = other)
            if (
                isinstance(pred, LiquidApp)
                and pred.fun == Name("&&", 0)
                and isinstance(pred.args[1], LiquidApp)
                and pred.args[1].fun == Name("==", 0)
                and pred.args[1].args[0] == LiquidVar(iname)
            ):
                rep = pred.args[1].args[1]
                subs_pred = substitution_in_liquid(pred.args[0], rep, iname)
                subs_seq = substitution_in_constraint(seq, rep, iname)
                rc = simplify_constraint(
                    Implication(Name("_", fresh_counter.fresh()), t_bool, subs_pred, subs_seq, loc=iloc)
                )
                return rc

            cont = simplify_constraint(seq)
            s = simplify_expr(pred)

            # Track whether the bound variable was used in the original conclusion
            iname_used_in_original = is_used(iname, cont)

            # Simplify the conclusion in the innermost constraint if it's a LiquidConstraint
            if isinstance(cont, LiquidConstraint):
                simplified_conclusion = simplify_implication_conclusion(s, cont.expr)
                # Only update if simplification changed something
                if simplified_conclusion != cont.expr:
                    cont = LiquidConstraint(simplify_expr(simplified_conclusion), loc=cont.loc)

            other_used_vars = [x for x in used_variables(s) if x != iname]
            # If the variable was not used in the original conclusion and there are no other free vars in premise,
            # we can drop the implication (the premise becomes irrelevant)
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


def simplify_constraint_fixpoint(c: Constraint, max_steps: int = 16) -> Constraint:
    """Apply simplification repeatedly until stable (or bounded)."""
    cur = c
    for _ in range(max_steps):
        nxt = simplify_constraint(cur)
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
            if is_used(iname, sseq):
                yield (f"∀{iname}:{base} | {pred}", 0)
            else:
                if pred != LiquidLiteralBool(True):
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
