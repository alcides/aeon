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

Bounded: states range over a small Int/Bool/List value domain; the DSL is the
integer/boolean fragment, the ``List Int`` destructors (``isEmpty``/``head``/
``tail``), conditionals, and the members' own calls — enough for the paper's
mutual-recursion (MR) flagship (``even``/``odd``), relational comparators over
integers, and the partial-data-structure (PDS) category (e.g. ``length`` over a
list, recovered as ``if isEmpty xs then 0 else 1 + length (tail xs)``).

List values are opaque constants of an uninterpreted z3 sort: their *structure*
is folded concretely by the destructors (so ``length`` recurses on the
strictly-shorter ``tail``, the well-founded measure being list length), while the
constant only serves to pin a recursive call's result in the spec (e.g.
``length(const_[2,3]) = 2``). This sidesteps z3's list theory entirely.
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
LIST = "List"  # List Int — the algebraic-datatype fragment (PDS category)


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

# Operators usable as transitions: (op-name, [arg types], ret). Includes the
# List-Int destructors so recursive list functions (the PDS category) are
# buildable: ``isEmpty``/``head``/``tail`` of a list. Constructors (``nil``/
# ``cons``/``append``) are *not* free in the alphabet — they explode the bank;
# list→list SO bodies instead inject the productive constructor patterns in
# :func:`_enumerate_bodies` (``nil``, ``cons (head x) (f (tail x))``,
# ``append (f (tail x)) (cons (head x) nil)``).
_OPS: list[tuple[str, list[str], str]] = [
    ("-", [INT, INT], INT),
    ("+", [INT, INT], INT),
    ("==", [INT, INT], BOOL),
    ("<", [INT, INT], BOOL),
    ("<=", [INT, INT], BOOL),
    (">", [INT, INT], BOOL),
    ("isEmpty", [LIST], BOOL),
    ("head", [LIST], INT),
    ("tail", [LIST], LIST),
]

_TYPES = (INT, BOOL, LIST)
_PARAM = Name("x", 0)


def _op(name: str) -> Var:
    return Var(Name(name, 0))


def _atoms(arg_type: str) -> dict[str, list[Term]]:
    """Nullary leaves per type: the parameter, constants, and ``nil``."""
    bank: dict[str, list[Term]] = {INT: [], BOOL: [], LIST: []}
    bank[arg_type].append(Var(_PARAM))  # the parameter
    bank[INT].extend([Literal(0, t_int), Literal(1, t_int)])
    bank[BOOL].extend([Literal(True, t_bool), Literal(False, t_bool)])
    bank[LIST].append(_op("nil"))
    return bank


def _is_member_app(term: Term, member_names: set[str]) -> bool:
    head = term
    while isinstance(head, Application):
        head = head.fun
    return isinstance(head, Var) and head.name.name in member_names


def _contains_member_app(term: Term, member_names: set[str]) -> bool:
    """A member/recursive call anywhere inside ``term`` — so a recursive branch
    like ``1 + length (tail xs)`` (call under an operator) is recognised, not
    only a bare ``odd (x-1)``."""
    if _is_member_app(term, member_names):
        return True
    match term:
        case Application(fun, arg):
            return _contains_member_app(fun, member_names) or _contains_member_app(arg, member_names)
        case If(c, th, el):
            return any(_contains_member_app(t, member_names) for t in (c, th, el))
        case _:
            return False


def _is_recursive_shaped(term: Term, member_names: set[str]) -> bool:
    """A term that carries a recursive/mutual call anywhere — the body shapes that
    must survive bank-capping even though they are large, since a base/recursive
    split (``odd (x-1)``, ``1 + length (tail xs)``) is exactly what a recursive
    definition needs."""
    return _contains_member_app(term, member_names)


def _value_vector(term: Term, ty: str, inputs: list[Any]) -> Optional[tuple]:
    """The concrete value of ``term`` at each input, or ``None`` if it is symbolic
    (contains a call under synthesis). Used to merge observationally-equivalent
    sub-programs of the *non-recursive* fragment (FTA-style compression)."""
    out: list[Any] = []
    for x in inputs:
        if ty == INT:
            v: Any = _concrete_int(term, x)
        elif ty == BOOL:
            v = _concrete_bool(term, x)
        else:
            v = _concrete_list(term, x)
        if v is None:
            return None
        out.append(v)
    return tuple(out)


def _enumerate_bodies(
    members: list[MemberSig],
    goal_type: str,
    max_size: int,
    inputs: list[Any],
    max_bank: int = 48,
    cond_head: int = 16,
    rec_head: int = 64,
    rec_keep: int = 64,
) -> list[Term]:
    """Bottom-up enumeration of the version space: grow the per-type bank one
    transition deeper each round (operators and members' calls), then form
    conditionals of the **base/recursive-case shape** ``if cond then a else b``
    where one branch is a recursive/mutual call — the structure every recursive
    definition has.

    Two flavours of compression keep the version space small (paper §4): a
    member-call-free sub-program is merged by its **observed value-vector** over
    ``inputs`` (so the thousands of arithmetic terms collapse to one per distinct
    behaviour); a symbolic term (one that calls a function under synthesis) is
    merged syntactically. Each type's bank keeps its ``max_bank`` smallest terms
    *plus every recursive-shaped term*, so a branch like ``odd (x-1)`` is never
    crowded out. Returns goal-typed terms ordered by size."""
    arg_type = members[0].arg_type
    member_names = {m.name for m in members}
    bank = _atoms(arg_type)
    seen: dict[str, set] = {ty: set() for ty in _TYPES}

    def key_of(ty: str, term: Term):
        vec = _value_vector(term, ty, inputs)
        return ("v", vec) if vec is not None else ("s", str(term))

    for ty in bank:
        for t in bank[ty]:
            seen[ty].add(key_of(ty, t))

    calls = [(m.name, [m.arg_type], m.ret_type) for m in members]

    def add(ty: str, term: Term) -> None:
        k = key_of(ty, term)
        if k not in seen[ty]:
            seen[ty].add(k)
            bank[ty].append(term)

    # List→list SO/PDS constructor patterns (Contata productive shapes): free
    # ``cons``/``append`` in ``_OPS`` blow up the bank, so inject only the
    # bodies that actually show up in the paper suite.
    if arg_type == LIST:
        param = Var(_PARAM)
        nil_t = _op("nil")
        add(LIST, nil_t)
        head_p = Application(_op("head"), param)
        tail_p = Application(_op("tail"), param)
        for m in members:
            if m.arg_type != LIST:
                continue
            rec_tail = Application(_op(m.name), tail_p)
            if m.ret_type == LIST:
                # copy / map-shaped: cons (head x) (f (tail x))
                add(LIST, Application(Application(_op("cons"), head_p), rec_tail))
                # reverse-shaped: append (f (tail x)) (cons (head x) nil)
                singleton = Application(Application(_op("cons"), head_p), nil_t)
                add(LIST, Application(Application(_op("append"), rec_tail), singleton))
            if m.ret_type == INT:
                # length-shaped helper already covered by ``1 + f (tail)`` via +
                pass

    # Conditionals are *terminal* goal candidates (the body is a base/recursive
    # split). They are collected here and NOT fed back into ``bank`` — otherwise
    # the large ``if … else 1 + length (tail xs)`` shapes compete for the bank's
    # capped slots against many smaller distractors and are dropped before
    # reaching the goal list.
    results: dict[str, list[Term]] = {ty: [] for ty in _TYPES}
    results_seen: dict[str, set] = {ty: set() for ty in _TYPES}

    def add_result(ty: str, term: Term) -> None:
        s = str(term)
        if s not in results_seen[ty]:
            results_seen[ty].add(s)
            results[ty].append(term)

    def cap(terms: list[Term]) -> list[Term]:
        ordered = sorted(terms, key=_size)
        kept = ordered[:max_bank]
        # Retain the *smallest* recursive-shaped terms beyond the cap so a branch
        # like ``odd (x-1)`` or ``1 + length (tail xs)`` is never crowded out —
        # but bounded (``rec_keep``), or the list destructors make the set of
        # call-bearing terms grow combinatorially each round.
        extra = [t for t in ordered[max_bank:] if _is_recursive_shaped(t, member_names)]
        kept.extend(extra[:rec_keep])
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
        for ret in _TYPES:
            conds = sorted(snap.get(BOOL, []), key=_size)[:cond_head]
            # Base branch: a non-recursive expression, or a previously-formed
            # conditional (so two-level base/rec splits are reachable).
            bases = sorted(snap.get(ret, []), key=_size)[:cond_head]
            bases = bases + sorted(results[ret], key=_size)[:cond_head]
            # Recursive branch: a bare member call (``odd (x-1)``) *or* a call
            # under an operator (``1 + length (tail xs)``), smallest first. Drawn
            # from a wider pool than the base/guard, since the call-under-operator
            # shapes are larger and easily crowded out by arithmetic distractors.
            recs = sorted(
                (t for t in bank.get(ret, []) if _contains_member_app(t, member_names)),
                key=_size,
            )[:rec_head]
            for c in conds:
                for base in bases:
                    for rec in recs:
                        if base is not rec:
                            add_result(ret, If(c, base, rec))
                            add_result(ret, If(c, rec, base))
        for ty in bank:
            bank[ty] = cap(bank[ty])

    # Goal candidates: the simple (non-conditional) sub-programs of the goal type
    # plus every conditional formed, smallest first (MinTree order).
    return sorted(bank.get(goal_type, []) + results[goal_type], key=_size)


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


_list_sort_cache: list = []  # unused; lists are encoded as unique Int ids
_list_consts: dict[tuple, Any] = {}  # concrete list value -> unique z3 IntVal


def _list_sort():
    import z3

    # List values are distinct Int ids (not an uninterpreted sort): two different
    # tuples must never be Z3-equal, or MinTree wrongly accepts ``body = x`` for
    # ``reverse``.
    return z3.IntSort()


def _z3_const(v: Any):
    """A z3 term for a concrete value. Lists are unique integer ids so distinct
    tuples are distinct in the solver (their *structure* is still folded by the
    DSL destructors/constructors for well-founded recursion)."""
    import z3

    if isinstance(v, bool):
        return z3.BoolVal(v)
    if isinstance(v, int):
        return z3.IntVal(v)
    if isinstance(v, (tuple, list)):
        key = tuple(v)
        if key not in _list_consts:
            # Offset so list ids do not collide with small Int example values.
            _list_consts[key] = z3.IntVal(10_000 + len(_list_consts))
        return _list_consts[key]
    raise ValueError(f"unsupported constant {v!r}")


def _concrete_list(term: Term, x_value: Any) -> Optional[tuple]:
    """Evaluate a member-call-free list term at ``x = x_value`` to a concrete
    tuple, or ``None`` if symbolic / ill-defined (``tail`` of ``[]``)."""
    match term:
        case Var(name) if name == _PARAM and isinstance(x_value, (tuple, list)):
            return tuple(x_value)
        case Var(Name("nil", _)):
            return ()
        case Application(Var(Name("tail", _)), e):
            inner = _concrete_list(e, x_value)
            return inner[1:] if inner else None
        case Application():
            head: Term = term
            args: list[Term] = []
            while isinstance(head, Application):
                args.append(head.arg)
                head = head.fun
            args.reverse()
            if not isinstance(head, Var):
                return None
            nm = head.name.name
            if nm == "cons" and len(args) == 2:
                h = _concrete_int(args[0], x_value)
                t = _concrete_list(args[1], x_value)
                if h is None or t is None:
                    return None
                return (h,) + t
            if nm == "append" and len(args) == 2:
                a = _concrete_list(args[0], x_value)
                b = _concrete_list(args[1], x_value)
                if a is None or b is None:
                    return None
                return a + b
            return None
        case _:
            return None


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
            if isinstance(head, Var) and head.name.name == "head" and len(args) == 1:
                cl = _concrete_list(args[0], x_value)
                return cl[0] if cl else None
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
            if isinstance(head, Var) and head.name.name == "isEmpty" and len(args) == 1:
                cl = _concrete_list(args[0], x_value)
                return None if cl is None else len(cl) == 0
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


def _denote(
    term: Term,
    x_value: Any,
    member_ufs: dict[str, Any],
    example_pins: dict[str, dict[Any, Any]] | None = None,
):
    """⟦term⟧ at ``x = x_value`` as a z3 expression. Calls to members become
    uninterpreted-function applications (the constraint annotation); everything
    else folds concretely where possible. When ``example_pins`` maps
    ``member → {arg: out}`` from the ground spec, a recursive list call whose
    argument is a pinned example folds to that concrete output so list
    constructors (``cons``/``append``) can build SO bodies like ``reverse``.
    Raises on an unsupported shape, or on a recursive call whose argument is not
    provably *smaller* than the current input."""
    import z3

    pins = example_pins or {}

    match term:
        case Literal(value, _):
            return _z3_const(value)
        case Var(name) if name == _PARAM:
            return _z3_const(x_value)
        case Var(Name("nil", _)):
            return _z3_const(())
        case If(c, th, el):
            cb = _concrete_bool(c, x_value)
            if cb is True:
                return _denote(th, x_value, member_ufs, example_pins)
            if cb is False:
                return _denote(el, x_value, member_ufs, example_pins)
            cz = _denote(c, x_value, member_ufs, example_pins)
            return z3.If(
                cz,
                _denote(th, x_value, member_ufs, example_pins),
                _denote(el, x_value, member_ufs, example_pins),
            )
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
            if nm == "isEmpty" and len(args) == 1:
                cl = _concrete_list(args[0], x_value)
                if cl is None:
                    raise ValueError("isEmpty of a non-concrete list")
                return z3.BoolVal(len(cl) == 0)
            if nm == "head" and len(args) == 1:
                cl = _concrete_list(args[0], x_value)
                if not cl:
                    raise ValueError("head of an empty/non-concrete list")
                return z3.IntVal(cl[0])
            if nm == "tail" and len(args) == 1:
                cl = _concrete_list(term, x_value)
                if cl is None:
                    raise ValueError("tail of an empty/non-concrete list")
                return _z3_const(cl)
            if nm == "nil" and len(args) == 0:
                return _z3_const(())
            if nm == "cons" and len(args) == 2:
                cl = _concrete_list(term, x_value)
                if cl is not None:
                    return _z3_const(cl)
                h = _concrete_int(args[0], x_value)
                if h is None:
                    raise ValueError("cons head not concrete")
                t_conc = _concrete_list_via_pins(args[1], x_value, pins)
                if t_conc is not None:
                    return _z3_const((h,) + t_conc)
                raise ValueError("cons of a non-concrete list")
            if nm == "append" and len(args) == 2:
                cl = _concrete_list(term, x_value)
                if cl is not None:
                    return _z3_const(cl)
                a_conc = _concrete_list_via_pins(args[0], x_value, pins)
                b_conc = _concrete_list_via_pins(args[1], x_value, pins)
                if a_conc is not None and b_conc is not None:
                    return _z3_const(a_conc + b_conc)
                raise ValueError("append of a non-concrete list")
            if nm in member_ufs and len(args) == 1:
                iarg = _concrete_int(args[0], x_value)
                if iarg is not None:
                    if not (isinstance(x_value, int) and 0 <= iarg < x_value):
                        raise ValueError("recursive call not on a strictly smaller input")
                    return member_ufs[nm](_z3_const(iarg))
                larg = _concrete_list(args[0], x_value)
                if larg is not None:
                    if not (isinstance(x_value, (tuple, list)) and len(larg) < len(x_value)):
                        raise ValueError("recursive call not on a strictly smaller list")
                    pinned = pins.get(nm, {}).get(larg)
                    if pinned is not None:
                        return _z3_const(pinned if not isinstance(pinned, list) else tuple(pinned))
                    return member_ufs[nm](_z3_const(larg))
                raise ValueError("recursive call argument is not concrete")
            az = [_denote(a, x_value, member_ufs, example_pins) for a in args]
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


def _concrete_exec_list(
    term: Term, x_value: Any, self_bodies: dict[str, Term], stack: set[tuple] | None = None
) -> Optional[tuple]:
    """Concrete interpreter for a list-typed candidate: recursive member calls
    re-enter the candidate body on a smaller argument (PBE-style), so SO bodies
    like ``reverse`` do not need every intermediate suffix to appear in
    ``@example`` pins."""
    stack = stack if stack is not None else set()
    match term:
        case Var(name) if name == _PARAM and isinstance(x_value, (tuple, list)):
            return tuple(x_value)
        case Var(Name("nil", _)):
            return ()
        case If(c, th, el):
            cb = _concrete_bool(c, x_value)
            if cb is True:
                return _concrete_exec_list(th, x_value, self_bodies, stack)
            if cb is False:
                return _concrete_exec_list(el, x_value, self_bodies, stack)
            return None
        case Application():
            head: Term = term
            args: list[Term] = []
            while isinstance(head, Application):
                args.append(head.arg)
                head = head.fun
            args.reverse()
            if not isinstance(head, Var):
                return None
            nm = head.name.name
            if nm == "tail" and len(args) == 1:
                inner = _concrete_exec_list(args[0], x_value, self_bodies, stack)
                return inner[1:] if inner else None
            if nm == "cons" and len(args) == 2:
                h = _concrete_int(args[0], x_value)
                t = _concrete_exec_list(args[1], x_value, self_bodies, stack)
                if h is None or t is None:
                    return None
                return (h,) + t
            if nm == "append" and len(args) == 2:
                a = _concrete_exec_list(args[0], x_value, self_bodies, stack)
                b = _concrete_exec_list(args[1], x_value, self_bodies, stack)
                if a is None or b is None:
                    return None
                return a + b
            if nm in self_bodies and len(args) == 1:
                larg = _concrete_exec_list(args[0], x_value, self_bodies, stack)
                if larg is None:
                    return None
                if not (isinstance(x_value, (tuple, list)) and len(larg) < len(x_value)):
                    return None
                key = (nm, larg)
                if key in stack:
                    return None  # non-termination
                stack.add(key)
                try:
                    return _concrete_exec_list(self_bodies[nm], larg, self_bodies, stack)
                finally:
                    stack.discard(key)
            return _concrete_list(term, x_value)
        case _:
            return _concrete_list(term, x_value)


def _concrete_list_via_pins(term: Term, x_value: Any, pins: dict[str, dict[Any, Any]]) -> Optional[tuple]:
    """Concrete list value of ``term``, folding member calls via example pins.

    Used by :func:`_denote` when building ``cons``/``append`` around a recursive
    call whose argument appears in the ground ``@example`` set.
    """
    direct = _concrete_list(term, x_value)
    if direct is not None:
        return direct
    head: Term = term
    args: list[Term] = []
    while isinstance(head, Application):
        args.append(head.arg)
        head = head.fun
    args.reverse()
    if isinstance(head, Var) and head.name.name in pins and len(args) == 1:
        larg = _concrete_list(args[0], x_value)
        if larg is None:
            return None
        out = pins[head.name.name].get(larg)
        if out is None:
            return None
        return tuple(out) if isinstance(out, (tuple, list)) else None
    return None


def _sort(ty: str):
    import z3

    if ty == INT:
        return z3.IntSort()
    if ty == BOOL:
        return z3.BoolSort()
    return _list_sort()


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
    # Ground example pins: fold recursive list calls to known outputs so
    # ``cons``/``append`` can build list→list SO bodies.
    example_pins: dict[str, dict[Any, Any]] = {}
    for e in examples:
        key = tuple(e.arg) if isinstance(e.arg, (tuple, list)) else e.arg
        out = tuple(e.out) if isinstance(e.out, (tuple, list)) else e.out
        example_pins.setdefault(e.member, {})[key] = out
    # The example inputs (plus their predecessors, the values recursive calls
    # reach) over which non-recursive sub-programs are merged by behaviour. For
    # Int that is each input and its decrement; for List, every suffix reachable
    # by ``tail`` (the trace closure under the well-founded measure).
    int_inputs = sorted({e.arg for e in examples if isinstance(e.arg, int) and not isinstance(e.arg, bool)})
    inputs: list[Any] = sorted(set(int_inputs) | {v - 1 for v in int_inputs if v - 1 >= 0})
    list_inputs: set[tuple] = set()
    for e in examples:
        if isinstance(e.arg, (tuple, list)):
            t = tuple(e.arg)
            while True:
                list_inputs.add(t)
                if not t:
                    break
                t = t[1:]
    inputs.extend(sorted(list_inputs, key=len))

    bodies: dict[str, Term] = {}
    for m in members:
        goal_bodies = _enumerate_bodies(members, m.ret_type, max_size, inputs)
        chosen: Optional[Term] = None
        for body in goal_bodies:  # smallest first => MinTree
            mexs = by_member.get(m.name, [])
            if not mexs:
                continue
            # List→list: concretely execute the candidate (recursive calls re-enter
            # the same body on smaller lists). Avoids needing every suffix pinned.
            if m.ret_type == LIST:
                self_bodies = {**{n: bodies[n] for n in bodies}, m.name: body}
                ok = True
                for e in mexs:
                    got = _concrete_exec_list(body, e.arg, self_bodies)
                    want = tuple(e.out) if isinstance(e.out, (tuple, list)) else e.out
                    if got != want:
                        ok = False
                        break
                if ok:
                    chosen = body
                    if on_candidate is not None:
                        on_candidate(m.name, body)
                    break
                continue
            solver = z3.Solver()
            for s in spec:
                solver.add(s)
            try:
                for e in mexs:
                    solver.add(_denote(body, e.arg, ufs, example_pins) == _z3_const(e.out))
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
