"""A genuine Constraint-Annotated Tree Automaton (CATA) version space (Contata).

This is the paper's algorithm, not the enumerate-and-typecheck approximation:

* A candidate body is a *tree* over a small Int/Bool DSL whose alphabet includes
  the *functions under synthesis* (recursion + mutual recursion).
* Each tree denotes, at a given input, a **z3 expression** over those functions
  treated as **uninterpreted functions** (the constraint annotation): a call
  ``g e`` becomes ``g_uf(⟦e⟧)``. No evaluation, so recursion never loops.
* A tree is **accepted under a model** (Def. 6) iff the specification together
  with the tree's denotation at every input is satisfiable — one z3 query.
* The **smallest** accepted tree is returned (MinTree, Def. 11). For a ``mutual``
  group every member is solved against the *same* complete spec, so the members
  are mutually consistent by construction (the paper's product across inputs and
  the global ``φ`` collapse to: be consistent with ``ψ``).

Bounded: states range over a small Int/Bool value domain; the DSL is the integer
/boolean fragment plus conditionals and the members' own calls — enough for the
paper's mutual-recursion (MR) flagship (``even``/``odd``) and relational
comparators over integers.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from typing import Any, Callable, Optional

from aeon.core.terms import Application, If, Literal, Term, Var
from aeon.core.types import t_bool, t_int
from aeon.utils.name import Name

INT = "Int"
BOOL = "Bool"


@dataclass(frozen=True)
class MemberSig:
    """A function under synthesis: ``name`` with a single ``arg_type`` argument
    and ``ret_type`` result (the MR/RC benchmarks are unary)."""

    name: str
    arg_type: str
    ret_type: str


@dataclass(frozen=True)
class Example:
    """A ground spec fact ``member(arg) = out`` (from an ``@example``)."""

    member: str
    arg: Any
    out: Any


@dataclass
class ContataResult:
    bodies: dict[str, Term]  # member name -> synthesized body (a Term in the param)
    param: Name  # the parameter the bodies are written in terms of


# ---------------------------------------------------------------------------
# DSL — the ranked alphabet of the tree automaton.
# ---------------------------------------------------------------------------

# Integer/boolean operators usable as transitions: (op-name, [arg types], ret).
_OPS: list[tuple[str, list[str], str]] = [
    ("-", [INT, INT], INT),
    ("+", [INT, INT], INT),
    ("==", [INT, INT], BOOL),
    ("<", [INT, INT], BOOL),
    ("<=", [INT, INT], BOOL),
    (">", [INT, INT], BOOL),
]

_PARAM = Name("x", 0)


def _op(name: str) -> Var:
    return Var(Name(name, 0))


def _atoms(arg_type: str) -> dict[str, list[Term]]:
    """Nullary leaves per type: the parameter and a few constants."""
    bank: dict[str, list[Term]] = {INT: [], BOOL: []}
    bank[arg_type].append(Var(_PARAM))  # the parameter
    bank[INT].extend([Literal(0, t_int), Literal(1, t_int)])
    bank[BOOL].extend([Literal(True, t_bool), Literal(False, t_bool)])
    return bank


def _is_member_app(term: Term, member_names: set[str]) -> bool:
    head = term
    while isinstance(head, Application):
        head = head.fun
    return isinstance(head, Var) and head.name.name in member_names


def _is_recursive_shaped(term: Term, member_names: set[str]) -> bool:
    """A recursive/mutual call, or a conditional with one — the body shapes that
    must survive bank-capping even though they are large, since a base/recursive
    split is exactly what a recursive definition needs."""
    if _is_member_app(term, member_names):
        return True
    if isinstance(term, If):
        return _is_recursive_shaped(term.then, member_names) or _is_recursive_shaped(term.otherwise, member_names)
    return False


def _enumerate_bodies(
    members: list[MemberSig], goal_type: str, max_size: int, max_bank: int = 48, cond_head: int = 16
) -> list[Term]:
    """Bottom-up enumeration of the version space: grow the per-type bank one
    transition deeper each round (operators and members' calls), then form
    conditionals of the **base/recursive-case shape** ``if cond then a else b``
    where one branch is a recursive/mutual call — the structure every recursive
    definition has. Each type's bank keeps its ``max_bank`` smallest terms *plus
    every member-call term* (so a recursive branch like ``odd (x-1)`` is never
    crowded out by smaller junk). Returns goal-typed terms ordered by size."""
    arg_type = members[0].arg_type
    member_names = {m.name for m in members}
    bank = _atoms(arg_type)
    seen: dict[str, set[str]] = {INT: set(), BOOL: set()}
    for ty in bank:
        for t in bank[ty]:
            seen[ty].add(str(t))

    calls = [(m.name, [m.arg_type], m.ret_type) for m in members]

    def add(ty: str, term: Term) -> None:
        k = str(term)
        if k not in seen[ty]:
            seen[ty].add(k)
            bank[ty].append(term)

    def cap(terms: list[Term]) -> list[Term]:
        ordered = sorted(terms, key=_size)
        kept = ordered[:max_bank]
        kept_keys = {str(t) for t in kept}
        for t in ordered[max_bank:]:
            if _is_recursive_shaped(t, member_names):  # retain recursive/mutual calls + base/rec splits
                kept.append(t)
                kept_keys.add(str(t))
        return kept

    for _round in range(max_size):
        snap = {ty: cap(ts) for ty, ts in bank.items()}
        for name, arg_tys, ret in _OPS + calls:
            pools = [snap.get(a, []) for a in arg_tys]
            if any(not p for p in pools):
                continue
            for combo in itertools.product(*pools):
                term: Term = _op(name)
                for a in combo:
                    term = Application(term, a)
                add(ret, term)
        # Base/recursive-case conditionals at every type.
        for ret in (INT, BOOL):
            conds = sorted(snap.get(BOOL, []), key=_size)[:cond_head]
            bases = sorted(snap.get(ret, []), key=_size)[:cond_head]
            recs = [t for t in bank.get(ret, []) if _is_member_app(t, member_names)]
            for c in conds:
                for base in bases:
                    for rec in recs:
                        if base is not rec:
                            add(ret, If(c, base, rec))
                            add(ret, If(c, rec, base))
        for ty in bank:
            bank[ty] = cap(bank[ty])

    return sorted(bank.get(goal_type, []), key=_size)


def _size(t: Term) -> int:
    match t:
        case Application(fun, arg):
            return _size(fun) + _size(arg)
        case If(c, th, el):
            return 1 + _size(c) + _size(th) + _size(el)
        case _:
            return 1


# ---------------------------------------------------------------------------
# Constraint-annotation denotation: a body's value at an input as a z3 term.
# ---------------------------------------------------------------------------


def _z3_const(v: Any):
    import z3

    if isinstance(v, bool):
        return z3.BoolVal(v)
    if isinstance(v, int):
        return z3.IntVal(v)
    raise ValueError(f"unsupported constant {v!r}")


def _concrete_int(term: Term, x_value: Any) -> Optional[int]:
    """Evaluate a member-call-free integer term at ``x = x_value`` to a concrete
    ``int``, or ``None`` if it is symbolic (contains a call under synthesis)."""
    match term:
        case Literal(value, _) if isinstance(value, int) and not isinstance(value, bool):
            return value
        case Var(name) if name == _PARAM and isinstance(x_value, int):
            return x_value
        case Application():
            head: Term = term
            args: list[Term] = []
            while isinstance(head, Application):
                args.append(head.arg)
                head = head.fun
            args.reverse()
            if isinstance(head, Var) and head.name.name in {"-", "+"} and len(args) == 2:
                a, b = _concrete_int(args[0], x_value), _concrete_int(args[1], x_value)
                if a is None or b is None:
                    return None
                return a - b if head.name.name == "-" else a + b
            return None
        case _:
            return None


def _concrete_bool(term: Term, x_value: Any) -> Optional[bool]:
    """Evaluate a member-call-free boolean term at ``x = x_value`` to a concrete
    ``bool``, or ``None`` if symbolic. Lets a conditional with a concrete guard
    fold to the taken branch (so the *untaken* branch — which may make an
    out-of-range recursive call — is never required well-founded)."""
    match term:
        case Literal(value, _) if isinstance(value, bool):
            return value
        case Application():
            head: Term = term
            args: list[Term] = []
            while isinstance(head, Application):
                args.append(head.arg)
                head = head.fun
            args.reverse()
            if isinstance(head, Var) and len(args) == 2:
                a, b = _concrete_int(args[0], x_value), _concrete_int(args[1], x_value)
                if a is None or b is None:
                    return None
                cmp = {
                    "==": lambda: a == b,
                    "<": lambda: a < b,
                    "<=": lambda: a <= b,
                    ">": lambda: a > b,
                    ">=": lambda: a >= b,
                }.get(head.name.name)
                return cmp() if cmp else None
            return None
        case _:
            return None


def _denote(term: Term, x_value: Any, member_ufs: dict[str, Any]):
    """⟦term⟧ at ``x = x_value`` as a z3 expression. Calls to members become
    uninterpreted-function applications (the constraint annotation); everything
    else folds concretely where possible. Raises on an unsupported shape, or on a
    recursive call whose argument is not provably *smaller* than the current
    input (the Function-Call rule's well-foundedness side condition ``v' ≺ v_in``,
    Fig. 5) — without which a self-consistent non-terminating body such as
    ``even(x) = even(x)`` would be wrongly accepted."""
    import z3

    match term:
        case Literal(value, _):
            return _z3_const(value)
        case Var(name) if name == _PARAM:
            return _z3_const(x_value)
        case If(c, th, el):
            cb = _concrete_bool(c, x_value)
            if cb is True:
                return _denote(th, x_value, member_ufs)
            if cb is False:
                return _denote(el, x_value, member_ufs)
            cz = _denote(c, x_value, member_ufs)
            return z3.If(cz, _denote(th, x_value, member_ufs), _denote(el, x_value, member_ufs))
        case Application():
            head: Term = term
            args: list[Term] = []
            while isinstance(head, Application):
                args.append(head.arg)
                head = head.fun
            args.reverse()
            if not isinstance(head, Var):
                raise ValueError(f"unsupported head {head}")
            nm = head.name.name
            if nm in member_ufs and len(args) == 1:
                # Well-foundedness: the argument must be a concrete value strictly
                # smaller (in the natural order on the bounded Nat domain) than the
                # current input. This both rules out non-terminating bodies and
                # keeps the call's argument concrete so the spec can pin it.
                arg_val = _concrete_int(args[0], x_value)
                if arg_val is None or not (isinstance(x_value, int) and 0 <= arg_val < x_value):
                    raise ValueError("recursive call not on a strictly smaller input")
                return member_ufs[nm](_z3_const(arg_val))
            az = [_denote(a, x_value, member_ufs) for a in args]
            ops = {
                "-": lambda: az[0] - az[1],
                "+": lambda: az[0] + az[1],
                "==": lambda: az[0] == az[1],
                "<": lambda: az[0] < az[1],
                "<=": lambda: az[0] <= az[1],
                ">": lambda: az[0] > az[1],
                ">=": lambda: az[0] >= az[1],
            }
            if nm in ops and len(az) == 2:
                return ops[nm]()
            raise ValueError(f"unsupported operator {nm}")
        case _:
            raise ValueError(f"unsupported term {term}")


def _sort(ty: str):
    import z3

    return z3.IntSort() if ty == INT else z3.BoolSort()


def _build_ufs(members: list[MemberSig]):
    import z3

    return {m.name: z3.Function(m.name, _sort(m.arg_type), _sort(m.ret_type)) for m in members}


def _spec_assertions(ufs, examples: list[Example]):
    return [ufs[e.member](_z3_const(e.arg)) == _z3_const(e.out) for e in examples]


def synthesize_group(
    members: list[MemberSig],
    examples: list[Example],
    max_size: int = 4,
    on_candidate: Optional[Callable[[str, Term], None]] = None,
) -> Optional[ContataResult]:
    """Synthesize every member of a (mutually-recursive) group from a ground
    relational/example spec, via the CATA version space.

    Each member is solved against the *complete* spec ``ψ`` (all members'
    examples): the smallest body whose constraint-annotated denotation agrees
    with the member's examples — under *some* model of ``ψ`` — at every example
    input. Because every member is consistent with the same ``ψ``, the group is
    mutually consistent. Returns ``None`` if any member has no accepted body
    within ``max_size``."""
    import z3

    ufs = _build_ufs(members)
    spec = _spec_assertions(ufs, examples)
    by_member: dict[str, list[Example]] = {}
    for e in examples:
        by_member.setdefault(e.member, []).append(e)

    bodies: dict[str, Term] = {}
    for m in members:
        goal_bodies = _enumerate_bodies(members, m.ret_type, max_size)
        chosen: Optional[Term] = None
        for body in goal_bodies:  # smallest first => MinTree
            mexs = by_member.get(m.name, [])
            if not mexs:
                continue
            solver = z3.Solver()
            for s in spec:
                solver.add(s)
            try:
                for e in mexs:
                    solver.add(_denote(body, e.arg, ufs) == _z3_const(e.out))
            except ValueError:
                continue  # body uses an unsupported shape; skip
            if solver.check() == z3.sat:
                chosen = body
                if on_candidate is not None:
                    on_candidate(m.name, body)
                break
        if chosen is None:
            return None
        bodies[m.name] = chosen
    return ContataResult(bodies=bodies, param=_PARAM)
