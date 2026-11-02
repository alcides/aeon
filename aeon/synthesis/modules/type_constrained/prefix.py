"""Bounded nondeterministic prefix automaton for ordinary Aeon expressions.

The worklist holds typed grammar continuations (precedence level, lexical
environment, remaining terminals). Matching a partial lexeme retains all its
possible completions. A LIVE answer includes an actual completion derivation;
running out of work never establishes DEAD. This is deliberately independent
of Aeon's whole-expression parser, which is used at final acceptance and in
differential tests, not to classify incomplete syntax.
"""

from __future__ import annotations

import ast
import math
from collections import OrderedDict
from dataclasses import dataclass
from enum import Enum
import re
from time import monotonic

from aeon.core.types import Type
from aeon.typechecking.context import TypingContext
from aeon.synthesis.modules.type_constrained.types import BOOL, FLOAT, INT, STRING, KEYWORDS, Mono, Scope


class Status(str, Enum):
    LIVE = "live"
    DEAD = "dead"
    UNKNOWN = "unknown"


@dataclass(frozen=True)
class Completion:
    status: Status
    witness: str | None = None
    accepting: bool = False
    explored: int = 0


@dataclass(frozen=True)
class State:
    text: str = ""


@dataclass(frozen=True)
class Limits:
    max_states: int = 20000
    max_chars: int = 2048
    max_stack: int = 128
    cache_size: int = 512

    def __post_init__(self):
        if min(self.max_states, self.max_chars, self.max_stack, self.cache_size) <= 0:
            raise ValueError("prefix limits must be positive")


Env = tuple[tuple[str, Mono], ...]


@dataclass(frozen=True)
class Expr:
    ty: Mono
    env: Env
    level: int = 0


@dataclass(frozen=True)
class Tail:
    ty: Mono
    env: Env
    level: int


@dataclass(frozen=True)
class Token:
    text: str
    kind: str = "fixed"


Task = Expr | Tail | Token


class _SearchLimit(Exception):
    pass


_WORD = re.compile(r"[A-Za-z_][A-Za-z_0-9]*")
_FLOAT = re.compile(r"[+-]?(?:[0-9]+\.[0-9]*|\.[0-9]+)(?:[eE][+-]?[0-9]+)?|[+-]?[0-9]+[eE][+-]?[0-9]+")
_NUMBER_PREFIX = re.compile(r"[+-]?(?:[0-9]*(?:\.[0-9]*)?)(?:[eE][+-]?[0-9]*)?\Z")


def _shadow(env: Env, name: str, ty: Mono) -> Env:
    return tuple((n, t) for n, t in env if n != name) + ((name, ty),)


def _binder(source: str, keyword: str) -> str | None:
    match = re.match(rf"{keyword}\s+([A-Za-z_][A-Za-z_0-9]*)", source)
    name = match[1] if match else "x"
    return name if name not in KEYWORDS else None


def _token_match(token: Token, text: str, complete: bool) -> tuple[int, str] | None:
    """Return consumed input and completed lexeme, without mutating a lexer."""
    whitespace = len(text) - len(text.lstrip(" \t\r\n\f"))
    rest = text[whitespace:]
    value = token.text
    if token.kind == "int":
        match = re.match(r"[0-9]+", rest)
        value = match[0] if match else "0"
    elif token.kind == "float":
        match = _FLOAT.match(rest)
        if match and (match.end() == len(rest) or not _NUMBER_PREFIX.fullmatch(rest)):
            value = match[0]
        elif complete and _NUMBER_PREFIX.fullmatch(rest):
            value = rest
            if not value or value in {"+", "-"}:
                value += "0.0"
            elif value[-1] in "eE+-":
                value += "0"
            elif "." not in value and "e" not in value.lower():
                value += ".0"
            elif value.endswith("."):
                value += "0"
            if not _FLOAT.fullmatch(value):
                return None
        else:
            return None
        if not math.isfinite(float(value)):
            return None
    elif token.kind == "string":
        if not rest:
            value = '""'
        elif rest[0] != '"':
            return None
        else:
            escaped = False
            end = None
            for i, char in enumerate(rest[1:], 1):
                if char in "\n\r":
                    return None
                if char == '"' and not escaped:
                    end = i + 1
                    break
                escaped = char == "\\" and not escaped
            value = rest[:end] if end is not None else rest
            if end is None:
                if not complete:
                    return None
                # Complete a pending Python/Aeon escape without changing bytes.
                escape = re.search(r"(?<!\\)(?:\\\\)*\\([xuU])([0-9a-fA-F]*)$", value)
                if escape:
                    width = {"x": 2, "u": 4, "U": 8}[escape[1]]
                    value += "0" * max(0, width - len(escape[2]))
                elif escaped:
                    value += "n"
                value += '"'
            try:
                ast.literal_eval(value)
            except (ValueError, SyntaxError, UnicodeError):
                return None
    if rest.startswith(value):
        # Aeon's identifiers and numbers must end at a lexical boundary. This
        # preserves both `f` and `foo` at EOF, without accepting `ftrue` as `f true`.
        end = len(value)
        if value and (value[-1].isalnum() or value[-1] == "_") and len(rest) > end:
            if rest[end].isalnum() or rest[end] in "_.":
                return None
        return whitespace + end, text[:whitespace] + value
    if complete and value.startswith(rest):
        return len(text), text[:whitespace] + value
    return None


class PrefixEngine:
    def __init__(self, scope: Scope, limits: Limits = Limits()):
        self.scope = scope
        self.limits = limits
        self._cache: OrderedDict[str, Completion] = OrderedDict()
        self._inhabit_cache: OrderedDict[tuple[Mono, Env], str] = OrderedDict()

    @classmethod
    def start(cls, context: TypingContext, expected_type: Type, limits: Limits = Limits()) -> PrefixEngine:
        return cls(Scope(context, expected_type), limits)

    def advance(self, state: State, characters: str) -> State:
        return State(state.text + characters)

    def is_accepting(self, state: State, deadline: float = float("inf")) -> bool:
        return self.completion_status(state, deadline).accepting

    def _operator(self, env: Env, spelling: str, arg: Mono, result: Mono) -> bool:
        internal = {"=": "==", "≠": "!=", "≤": "<=", "≥": ">="}.get(spelling, spelling)
        signature = Mono("->", arg, Mono("->", arg, result))
        return (internal, signature) in env

    def _inhabit(
        self,
        ty: Mono,
        env: Env,
        fuel: list[int],
        deadline: float,
        seen: frozenset[tuple[Mono, frozenset[Mono]]] = frozenset(),
    ) -> str | None:
        """Cache successful derivations only; cyclic partial failures are local."""
        if fuel[0] <= 0 or monotonic() >= deadline:
            raise _SearchLimit
        key = (ty, env)
        if key in self._inhabit_cache:
            fuel[0] -= 1
            self._inhabit_cache.move_to_end(key)
            return self._inhabit_cache[key]
        witness = self._derive_witness(ty, env, fuel, deadline, seen)
        if witness is not None:
            self._inhabit_cache[key] = witness
            while len(self._inhabit_cache) > self.limits.cache_size:
                self._inhabit_cache.popitem(last=False)
        return witness

    def _derive_witness(
        self,
        ty: Mono,
        env: Env,
        fuel: list[int],
        deadline: float,
        seen: frozenset[tuple[Mono, frozenset[Mono]]],
    ) -> str | None:
        """Bounded type reachability, returning a derivation rather than a guess."""
        if fuel[0] <= 0 or monotonic() >= deadline:
            raise _SearchLimit
        fuel[0] -= 1
        for name, available in env:
            if available == ty and name not in self._operator_names:
                return name
        literals = {INT: "0", BOOL: "true", FLOAT: "0.0", STRING: '""'}
        if ty in literals:
            return literals[ty]
        judgement = (ty, frozenset(t for n, t in env if n not in self._operator_names))
        if judgement in seen:
            return None
        seen = seen | {judgement}
        if ty.arg is not None and ty.result is not None:
            name = "x"
            while any(n == name for n, _ in env):
                name += "x"
            body = self._inhabit(ty.result, _shadow(env, name, ty.arg), fuel, deadline, seen)
            if body is not None:
                return f"(fun {name} => {body})"
        for name, available in env:
            if name in self._operator_names:
                continue
            args: list[str] = []
            while available.arg is not None and available.result is not None:
                arg = self._inhabit(available.arg, env, fuel, deadline, seen)
                if arg is None:
                    break
                args.append(f"({arg})")
                available = available.result
                if available == ty:
                    return " ".join([name, *args])
        return None

    _operator_names = frozenset({"+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "!=", "&&", "||", "-->", "!"})

    def _rules(self, task: Expr | Tail, rest: str) -> list[tuple[Task, ...]]:
        ty, env, level = task.ty, task.env, task.level

        def ex(t: Mono, level: int = 0) -> Expr:
            return Expr(t, env, level)

        def tok(s: str) -> Token:
            return Token(s)

        if isinstance(task, Tail):
            ops = {1: ("-->",), 2: ("||",), 3: ("&&",), 7: ("+", "-"), 8: ("*", "/", "%")}[level]
            return [()] + [(tok(op), ex(ty, level + 1), task) for op in ops if self._operator(env, op, ty, ty)]
        rules: list[tuple[Task, ...]] = []
        if level == 0:
            rules.append((ex(ty, 1),))
            rules.append((tok("if"), ex(BOOL), tok("then"), ex(ty), tok("else"), ex(ty)))
            binder = _binder(rest, "let")
            if binder is not None:
                for value_type in self.scope.universe:
                    body = Expr(ty, _shadow(env, binder, value_type))
                    for separator in ("in", ";"):
                        rules.append((tok("let"), tok(binder), tok(":="), ex(value_type), tok(separator), body))
        elif level in {1, 2, 3, 7, 8}:
            rules.append((ex(ty, level + 1), Tail(ty, env, level)))
        elif level == 4:
            rules.append((ex(ty, 5),))
            if ty == BOOL:
                for domain in (INT, FLOAT, BOOL, STRING):
                    for op in ("=", "!=", "≠"):
                        if self._operator(env, op, domain, BOOL):
                            rules.append((ex(domain, 5), tok(op), ex(domain, 5)))
        elif level == 5:
            rules.append((ex(ty, 6),))
            if ty == BOOL and ("!", Mono("->", BOOL, BOOL)) in env:
                rules.append((tok("!"), ex(BOOL, 5)))
        elif level == 6:
            rules.append((ex(ty, 7),))
            if ty == BOOL:
                for domain in (INT, FLOAT):
                    for op in ("<", "<=", ">", ">=", "≤", "≥"):
                        if self._operator(env, op, domain, BOOL):
                            rules.append((ex(domain, 7), tok(op), ex(domain, 7)))
        elif level == 9:
            rules.append((ex(ty, 10),))
            if ty.arg is not None and ty.result is not None:
                binder = _binder(rest, "fun")
                if binder is not None:
                    rules.append((tok("fun"), tok(binder), tok("=>"), Expr(ty.result, _shadow(env, binder, ty.arg))))
            # A head remains viable if applying inhabitable argument types
            # reaches the goal. Arguments are atoms, matching Aeon's grammar.
            for name, available in env:
                if name in self._operator_names:
                    continue
                args: list[Task] = []
                while available.arg is not None and available.result is not None:
                    args.append(ex(available.arg, 10))
                    available = available.result
                    if available == ty:
                        rules.append((tok(name), *args))
            # Parenthesized function expressions may also be applied. The
            # finite universe contains subtypes of the goal and components.
            for function in self.scope.universe:
                args = []
                available = function
                while available.arg is not None and available.result is not None:
                    args.append(ex(available.arg, 10))
                    available = available.result
                    if available == ty:
                        rules.append((tok("("), ex(function), tok(")"), *args))
        elif level == 10:
            rules.extend(
                (tok(name),) for name, available in env if available == ty and name not in self._operator_names
            )
            if ty == INT:
                rules.append((Token("", "int"),))
            elif ty == FLOAT:
                rules.append((Token("", "float"),))
            elif ty == STRING:
                rules.append((Token("", "string"),))
            elif ty == BOOL:
                rules.extend([(tok("true"),), (tok("false"),)])
            rules.append((tok("("), ex(ty), tok(")")))
        return rules

    def _search(self, source: str, complete: bool, deadline: float, allowance: int) -> tuple[str | None, int, bool]:
        stack: list[tuple[tuple[Task, ...], int, str]] = [((Expr(self.scope.expected, self.scope.environment),), 0, "")]
        visited: set[tuple[tuple[Task, ...], int]] = set()
        count = 0
        exhausted = False
        while stack:
            if count >= allowance or monotonic() >= deadline:
                return None, count, True
            tasks, pos, output = stack.pop()
            count += 1
            if len(tasks) > self.limits.max_stack:
                exhausted = True
                continue
            # A continuation's future depends only on its environment/grammar
            # and input offset; spelling of a previously completed witness does
            # not affect typing. Each engine owns its environment and cache.
            key = (tasks, pos)
            if key in visited:
                continue
            visited.add(key)
            rest = source[pos:]
            if not tasks:
                if not rest.strip(" \t\r\n\f"):
                    return output + rest, count, exhausted
                continue
            task, tail = tasks[0], tasks[1:]
            if isinstance(task, Token):
                result = _token_match(task, rest, complete)
                if result is not None:
                    consumed, rendered = result
                    # Separate generated lexemes. Existing input bytes are
                    # always preserved, including partial identifiers/escapes.
                    space = " " if not rest and output and not output[-1].isspace() else ""
                    stack.append((tail, pos + consumed, output + space + rendered))
                continue
            if not rest.strip(" \t\r\n\f") and isinstance(task, Expr):
                if complete:
                    fuel = [allowance - count]
                    try:
                        witness = self._inhabit(task.ty, task.env, fuel, deadline)
                    except _SearchLimit:
                        return None, allowance, True
                    count = allowance - fuel[0]
                    if witness is not None:
                        if task.level == 10 and " " in witness:
                            witness = f"({witness})"
                        gap = rest or (" " if output and not output[-1].isspace() else "")
                        stack.append((tail, len(source), output + gap + witness))
                continue
            rules = self._rules(task, rest.lstrip(" \t\r\n\f"))
            for rule in reversed(rules):
                stack.append((rule + tail, pos, output))
        return None, count, exhausted

    def completion_status(self, state: State, deadline: float = float("inf")) -> Completion:
        if monotonic() >= deadline or len(state.text) > self.limits.max_chars:
            return Completion(Status.UNKNOWN)
        if state.text in self._cache:
            self._cache.move_to_end(state.text)
            return self._cache[state.text]
        witness, count, exhausted = self._search(state.text, False, deadline, self.limits.max_states // 2)
        accepting = witness is not None
        if not accepting:
            witness, extra, stopped = self._search(state.text, True, deadline, self.limits.max_states - count)
            count += extra
            exhausted = exhausted or stopped
        status = Status.LIVE if witness is not None else Status.UNKNOWN if exhausted else Status.DEAD
        answer = Completion(status, witness, accepting, count)
        # Time/resource-dependent UNKNOWN results must not poison later probes.
        if status is not Status.UNKNOWN:
            self._cache[state.text] = answer
            while len(self._cache) > self.limits.cache_size:
                self._cache.popitem(last=False)
        return answer
