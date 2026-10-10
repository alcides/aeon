"""Typed reader and interpreter for Absynthe's SyGuS string benchmarks.

The original Absynthe artifact supplies ``.sl`` files but does not expose a
parser.  Keeping this small, dependency-free reader separate from Aeon's
source parser lets synthesis backends use the benchmark format directly.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from pathlib import Path
import re
from typing import TypeAlias


class Sort(str, Enum):
    STRING = "String"
    INT = "Int"
    BOOL = "Bool"


Value: TypeAlias = str | int | bool


class SygusError(ValueError):
    """Raised for malformed or ill-typed supported SyGuS input."""


@dataclass(frozen=True)
class Symbol:
    value: str


@dataclass(frozen=True)
class String:
    value: str


SExpr: TypeAlias = Symbol | String | list["SExpr"]


@dataclass(frozen=True)
class Literal:
    value: Value


@dataclass(frozen=True)
class Variable:
    name: str


@dataclass(frozen=True)
class Apply:
    operator: str
    arguments: tuple["Expression", ...]


@dataclass(frozen=True)
class IfThenElse:
    condition: "Expression"
    then_branch: "Expression"
    else_branch: "Expression"


Expression: TypeAlias = Literal | Variable | Apply | IfThenElse


@dataclass(frozen=True)
class GrammarRule:
    name: str
    sort: Sort
    productions: tuple[SExpr, ...]


@dataclass(frozen=True)
class ExampleConstraint:
    inputs: tuple[Value, ...]
    expected: Value


@dataclass(frozen=True)
class Benchmark:
    """A typed synthesis target plus its input/output constraints."""

    name: str
    parameters: tuple[tuple[str, Sort], ...]
    result_sort: Sort
    grammar: tuple[GrammarRule, ...]
    constraints: tuple[ExampleConstraint, ...]
    source: str = ""

    @property
    def parameter_sorts(self) -> dict[str, Sort]:
        return dict(self.parameters)

    def validate(self, expression: Expression) -> None:
        actual = infer_sort(expression, self.parameter_sorts)
        if actual != self.result_sort:
            raise SygusError(f"candidate returns {actual.value}, expected {self.result_sort.value}")

    def evaluate(self, expression: Expression, inputs: tuple[Value, ...]) -> Value:
        self.validate(expression)
        if len(inputs) != len(self.parameters):
            raise SygusError(f"expected {len(self.parameters)} inputs, got {len(inputs)}")
        environment = dict(zip((name for name, _ in self.parameters), inputs, strict=True))
        for (name, sort), value in zip(self.parameters, inputs, strict=True):
            if sort_of(value) != sort:
                raise SygusError(f"input {name} has type {sort_of(value).value}, expected {sort.value}")
        return evaluate(expression, environment)

    def violated_constraints(self, expression: Expression) -> tuple[ExampleConstraint, ...]:
        try:
            self.validate(expression)
        except SygusError:
            return self.constraints
        failed = []
        for constraint in self.constraints:
            try:
                if self.evaluate(expression, constraint.inputs) != constraint.expected:
                    failed.append(constraint)
            except SygusError:
                failed.append(constraint)
        return tuple(failed)

    def fitness(self, expression: Expression) -> int:
        """Number of unsatisfied examples; zero is an exact target."""
        return len(self.violated_constraints(expression))

    def satisfies(self, expression: Expression) -> bool:
        return self.fitness(expression) == 0


_SIGNATURES: dict[str, tuple[tuple[Sort, ...], Sort]] = {
    "str.++": ((Sort.STRING, Sort.STRING), Sort.STRING),
    "str.replace": ((Sort.STRING, Sort.STRING, Sort.STRING), Sort.STRING),
    "str.substr": ((Sort.STRING, Sort.INT, Sort.INT), Sort.STRING),
    "str.at": ((Sort.STRING, Sort.INT), Sort.STRING),
    "int.to.str": ((Sort.INT,), Sort.STRING),
    "+": ((Sort.INT, Sort.INT), Sort.INT),
    "-": ((Sort.INT, Sort.INT), Sort.INT),
    "str.len": ((Sort.STRING,), Sort.INT),
    "str.to.int": ((Sort.STRING,), Sort.INT),
    "str.indexof": ((Sort.STRING, Sort.STRING, Sort.INT), Sort.INT),
    "str.prefixof": ((Sort.STRING, Sort.STRING), Sort.BOOL),
    "str.suffixof": ((Sort.STRING, Sort.STRING), Sort.BOOL),
    "str.contains": ((Sort.STRING, Sort.STRING), Sort.BOOL),
}


def sort_of(value: Value) -> Sort:
    if type(value) is bool:
        return Sort.BOOL
    if type(value) is int:
        return Sort.INT
    if type(value) is str:
        return Sort.STRING
    raise SygusError(f"unsupported value {value!r}")


def infer_sort(expression: Expression, variables: dict[str, Sort]) -> Sort:
    if isinstance(expression, Literal):
        return sort_of(expression.value)
    if isinstance(expression, Variable):
        try:
            return variables[expression.name]
        except KeyError as error:
            raise SygusError(f"unknown variable {expression.name!r}") from error
    if isinstance(expression, IfThenElse):
        if infer_sort(expression.condition, variables) != Sort.BOOL:
            raise SygusError("ite condition must be Bool")
        then_sort = infer_sort(expression.then_branch, variables)
        else_sort = infer_sort(expression.else_branch, variables)
        if then_sort != else_sort:
            raise SygusError("ite branches must have the same sort")
        return then_sort
    if expression.operator not in _SIGNATURES:
        raise SygusError(f"unsupported operator {expression.operator!r}")
    expected, result = _SIGNATURES[expression.operator]
    actual = tuple(infer_sort(argument, variables) for argument in expression.arguments)
    if actual != expected:
        raise SygusError(
            f"{expression.operator} expects ({', '.join(x.value for x in expected)}), "
            f"got ({', '.join(x.value for x in actual)})"
        )
    return result


def evaluate(expression: Expression, environment: dict[str, Value]) -> Value:
    if isinstance(expression, Literal):
        return expression.value
    if isinstance(expression, Variable):
        try:
            return environment[expression.name]
        except KeyError as error:
            raise SygusError(f"unknown variable {expression.name!r}") from error
    if isinstance(expression, IfThenElse):
        condition = evaluate(expression.condition, environment)
        if type(condition) is not bool:
            raise SygusError("ite condition must be Bool")
        return evaluate(expression.then_branch if condition else expression.else_branch, environment)

    values = tuple(evaluate(argument, environment) for argument in expression.arguments)
    operator = expression.operator
    if operator == "str.++":
        return _string(values[0]) + _string(values[1])
    if operator == "str.replace":
        return _string(values[0]).replace(_string(values[1]), _string(values[2]), 1)
    if operator == "str.substr":
        string, start, length = _string(values[0]), _integer(values[1]), _integer(values[2])
        if start < 0 or length <= 0 or start >= len(string):
            return ""
        return string[start : start + length]
    if operator == "str.at":
        string, index = _string(values[0]), _integer(values[1])
        return string[index] if 0 <= index < len(string) else ""
    if operator == "int.to.str":
        value = _integer(values[0])
        return str(value) if value >= 0 else ""
    if operator == "+":
        return _integer(values[0]) + _integer(values[1])
    if operator == "-":
        return _integer(values[0]) - _integer(values[1])
    if operator == "str.len":
        return len(_string(values[0]))
    if operator == "str.to.int":
        string_value = _string(values[0])
        return int(string_value) if string_value.isdecimal() else -1
    if operator == "str.indexof":
        string, needle, start = _string(values[0]), _string(values[1]), _integer(values[2])
        return string.find(needle, start) if 0 <= start <= len(string) else -1
    if operator == "str.prefixof":
        return _string(values[1]).startswith(_string(values[0]))
    if operator == "str.suffixof":
        return _string(values[1]).endswith(_string(values[0]))
    if operator == "str.contains":
        return _string(values[0]) in _string(values[1])
    raise SygusError(f"unsupported operator {operator!r}")


def parse_expression(source: str) -> Expression:
    forms = parse_sexpressions(source)
    if len(forms) != 1:
        raise SygusError("expected exactly one expression")
    return _expression(forms[0])


def load_benchmark(path: str | Path) -> Benchmark:
    source = Path(path).read_text(encoding="utf-8")
    return parse_benchmark(source, source=str(path))


def parse_benchmark(text: str, source: str = "") -> Benchmark:
    forms = parse_sexpressions(text)
    synth = next((form for form in forms if _head(form) == "synth-fun"), None)
    if synth is None:
        raise SygusError("expected one (synth-fun name (...) Sort (...)) declaration")
    synth_values = _list(synth)
    if len(synth_values) != 5:
        raise SygusError("expected one (synth-fun name (...) Sort (...)) declaration")
    name = _symbol(synth_values[1])
    parameters = tuple(_parameter(pair) for pair in _list(synth_values[2]))
    result_sort = _sort(synth_values[3])
    grammar = tuple(_grammar_rule(rule) for rule in _list(synth_values[4]))
    constraints = tuple(_constraint(form, name) for form in forms if _head(form) == "constraint")
    if not constraints:
        raise SygusError("benchmark has no constraints")
    return Benchmark(name, parameters, result_sort, grammar, constraints, source)


def parse_sexpressions(text: str) -> list[SExpr]:
    tokens = _tokens(text)
    position = 0

    def parse_one() -> SExpr:
        nonlocal position
        if position >= len(tokens):
            raise SygusError("unexpected end of input")
        token = tokens[position]
        position += 1
        if token == "(":
            result: list[SExpr] = []
            while position < len(tokens) and tokens[position] != ")":
                result.append(parse_one())
            if position == len(tokens):
                raise SygusError("unclosed parenthesis")
            position += 1
            return result
        if token == ")":
            raise SygusError("unexpected closing parenthesis")
        if isinstance(token, (Symbol, String)):
            return token
        raise SygusError(f"unexpected token {token!r}")

    forms = []
    while position < len(tokens):
        forms.append(parse_one())
    return forms


def _tokens(text: str) -> list[str | String | Symbol]:
    tokens: list[str | String | Symbol] = []
    index = 0
    while index < len(text):
        char = text[index]
        if char.isspace():
            index += 1
        elif char == ";":
            index = text.find("\n", index)
            if index == -1:
                break
        elif char in "()":
            tokens.append(char)
            index += 1
        elif char == '"':
            index += 1
            value = []
            while index < len(text) and text[index] != '"':
                if text[index] == "\\" and index + 1 < len(text):
                    index += 1
                value.append(text[index])
                index += 1
            if index == len(text):
                raise SygusError("unterminated string")
            tokens.append(String("".join(value)))
            index += 1
        else:
            end = index
            while end < len(text) and not text[end].isspace() and text[end] not in "();":
                end += 1
            tokens.append(Symbol(text[index:end]))
            index = end
    return tokens


def _string(value: Value) -> str:
    if type(value) is not str:
        raise SygusError(f"expected String, got {sort_of(value).value}")
    return value


def _integer(value: Value) -> int:
    if type(value) is not int:
        raise SygusError(f"expected Int, got {sort_of(value).value}")
    return value


def _expression(form: SExpr) -> Expression:
    if isinstance(form, String):
        return Literal(form.value)
    if isinstance(form, Symbol):
        if form.value == "true":
            return Literal(True)
        if form.value == "false":
            return Literal(False)
        if re.fullmatch(r"-?\d+", form.value):
            return Literal(int(form.value))
        return Variable(form.value)
    if not form:
        raise SygusError("empty expression")
    operator = _symbol(form[0])
    arguments = tuple(_expression(argument) for argument in form[1:])
    if operator == "ite":
        if len(arguments) != 3:
            raise SygusError("ite expects three arguments")
        return IfThenElse(*arguments)
    return Apply(operator, arguments)


def _grammar_rule(form: SExpr) -> GrammarRule:
    values = _list(form)
    if len(values) != 3:
        raise SygusError("grammar rules need a name, sort, and production list")
    return GrammarRule(_symbol(values[0]), _sort(values[1]), tuple(_list(values[2])))


def _parameter(form: SExpr) -> tuple[str, Sort]:
    values = _list(form)
    if len(values) != 2:
        raise SygusError("parameters need a name and sort")
    return _symbol(values[0]), _sort(values[1])


def _constraint(form: SExpr, function_name: str) -> ExampleConstraint:
    values = _list(form)
    if len(values) != 2:
        raise SygusError("constraint expects one formula")
    equality = _list(values[1])
    if len(equality) != 3 or _symbol(equality[0]) != "=":
        raise SygusError("only equality example constraints are supported")
    left, right = equality[1:]
    if isinstance(right, list) and not isinstance(left, list):
        left, right = right, left
    call = _list(left)
    if not call or _symbol(call[0]) != function_name:
        raise SygusError("constraint must call the synthesized function")
    return ExampleConstraint(tuple(_concrete_value(value) for value in call[1:]), _concrete_value(right))


def _concrete_value(form: SExpr) -> Value:
    expression = _expression(form)
    if not isinstance(expression, Literal):
        raise SygusError("example inputs and outputs must be literals")
    return expression.value


def _sort(form: SExpr) -> Sort:
    try:
        return Sort(_symbol(form))
    except ValueError as error:
        raise SygusError(f"unsupported sort {_symbol(form)!r}") from error


def _head(form: SExpr) -> str | None:
    return _symbol(form[0]) if isinstance(form, list) and form else None


def _symbol(form: SExpr) -> str:
    if not isinstance(form, Symbol):
        raise SygusError(f"expected symbol, got {form!r}")
    return form.value


def _list(form: SExpr) -> list[SExpr]:
    if not isinstance(form, list):
        raise SygusError(f"expected list, got {form!r}")
    return form
