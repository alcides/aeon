"""Translate prepared FlatZinc constraints to pure Aeon expressions and holes.

FlatZinc is used only as a compiler interchange format during authoring, never
as a runtime solver or an opaque native model. Unsupported operations fail
explicitly. Every emitted constraint has its own named Bool definition.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re

from scripts.generate_hakank_examples import Model, conjunction, disjunction, indicator, total
from scripts.hakank_domains import infer_domains


class Unsupported(ValueError):
    pass


@dataclass(frozen=True)
class Variable:
    name: str
    lower: int | float
    upper: int | float
    boolean: bool = False
    floating: bool = False


@dataclass(frozen=True)
class SetVariable:
    members: dict[int, Variable]


def split_arguments(text: str) -> list[str]:
    depth, start, result = 0, 0, []
    for i, character in enumerate(text):
        if character in "[{(":
            depth += 1
        elif character in "]})":
            depth -= 1
        elif character == "," and depth == 0:
            result.append(text[start:i].strip())
            start = i + 1
    if text[start:].strip():
        result.append(text[start:].strip())
    return result


class Translator:
    def __init__(self, name: str, text: str, infer_bounds: bool = True):
        self.model = Model(name, "compiled finite-domain source instance")
        self.model.generator = "scripts/import_hakank_flatzinc.py"
        self.values: dict[str, object] = {}
        self.constraints: list[str] = []
        self.direction = "satisfy"
        self.target: object = None
        if infer_bounds:
            text = infer_domains(text, split_arguments)
        self.statements = [s.strip() for s in re.sub(r"%[^\n]*", "", text).split(";") if s.strip()]

    def value(self, text: str):
        text = text.strip()
        if text in self.values:
            return self.values[text]
        if text.startswith("[") and text.endswith("]"):
            return [self.value(item) for item in split_arguments(text[1:-1])]
        if text in ("true", "false"):
            return text == "true"
        if re.fullmatch(r"-?\d+", text):
            return int(text)
        if re.fullmatch(r"-?\d+\.\d+(?:[Ee][+-]?\d+)?", text):
            return float(text)
        if text.startswith("{"):
            return frozenset(self.value(item) for item in split_arguments(text[1:-1]))
        if matched := re.fullmatch(r"(-?\d+)\.\.(-?\d+)", text):
            return frozenset(range(int(matched[1]), int(matched[2]) + 1))
        raise Unsupported(f"value {text!r}")

    @staticmethod
    def number(value) -> str:
        if isinstance(value, Variable) and not value.boolean:
            return value.name
        if type(value) is int:
            return str(value) if value >= 0 else f"(0 - {-value})"
        if type(value) is float:
            return str(value) if value >= 0 else f"(0.0 - {-value})"
        raise Unsupported(f"numeric expression {value!r}")

    @staticmethod
    def boolean(value) -> str:
        if isinstance(value, Variable) and value.boolean:
            return value.name
        if type(value) is bool:
            return "true" if value else "false"
        raise Unsupported(f"Boolean expression {value!r}")

    @staticmethod
    def universe(value):
        if isinstance(value, SetVariable):
            return set(value.members)
        if isinstance(value, frozenset):
            return set(value)
        raise Unsupported("non-finite set expression")

    def member(self, value, item):
        if isinstance(value, SetVariable):
            return self.boolean(value.members[item]) if item in value.members else "false"
        if isinstance(value, frozenset):
            return "true" if item in value else "false"
        raise Unsupported("non-finite set expression")

    def set_equal(self, left, right):
        return conjunction(
            [
                f"{self.member(left, item)} = {self.member(right, item)}"
                for item in sorted(self.universe(left) | self.universe(right))
            ]
        )

    def relation(self, operation: str, args: list) -> str:
        suffix = ""
        if operation.endswith(("_reif", "_imp")):
            operation, suffix = operation.rsplit("_", 1)
        reification = args[-1] if suffix else None
        if suffix:
            args = args[:-1]
        comparisons = {"eq": "=", "ne": "!=", "le": "<=", "lt": "<", "ge": ">=", "gt": ">"}
        result: str
        if operation.startswith(("int_lin_", "float_lin_")):
            coefficients, variables, target = args
            if len(coefficients) != len(variables):
                raise Unsupported("linear coefficient/variable length mismatch")
            terms = [f"{self.number(c)} * {self.number(v)}" for c, v in zip(coefficients, variables)]
            expression = total(terms)
            if operation.startswith("int_lin_") and len(variables) >= 4:
                cs = self.model.sequence([self.number(c) for c in coefficients])
                vs = self.model.sequence([self.number(v) for v in variables])
                expression = f"Vec.dot ({cs}) ({vs})"
            result = f"{expression} {comparisons[operation.split('_lin_')[1]]} {self.number(target)}"
        elif operation.startswith(("int_", "float_")) and operation.split("_", 1)[1] in comparisons:
            result = f"{self.number(args[0])} {comparisons[operation.split('_', 1)[1]]} {self.number(args[1])}"
        elif operation in ("int_plus", "int_minus", "int_times", "float_plus", "float_minus", "float_times"):
            symbol = {"plus": "+", "minus": "-", "times": "*"}[operation.split("_", 1)[1]]
            result = f"{self.number(args[2])} = ({self.number(args[0])} {symbol} {self.number(args[1])})"
        elif operation == "int2float":
            result = f"{self.number(args[1])} = Vec.toFloat ({self.number(args[0])})"
        elif operation == "float_abs":
            a, b = map(self.number, args)
            result = f"{b} = (if {a} < 0.0 then (0.0 - {a}) else {a})"
        elif operation == "float_div":
            a, b, c = map(self.number, args)
            result = f"{b} != 0.0 && {a} = ({b} * {c})"
        elif operation == "int_abs":
            result = f"{self.number(args[1])} = Vec.absolute ({self.number(args[0])})"
        elif operation in ("int_min", "int_max"):
            a, b, c = map(self.number, args)
            symbol = "<=" if operation == "int_min" else ">="
            result = f"{c} = (if {a} {symbol} {b} then {a} else {b})"
        elif operation in ("int_div", "int_mod"):
            if suffix:
                raise Unsupported("reified division requires a functional encoding")
            a, b, c = args

            def magnitude(value):
                if type(value) is int:
                    return abs(value)
                if isinstance(value, Variable) and not value.boolean:
                    return max(abs(value.lower), abs(value.upper))
                raise Unsupported("division with non-integer operands")

            bound = magnitude(b) if operation == "int_div" else magnitude(a)
            name = f"division_aux{len(self.model.variables)}"
            self.model.variables[name] = [-bound, bound]
            auxiliary = Variable(name, -bound, bound)
            quotient, remainder = (c, auxiliary) if operation == "int_div" else (auxiliary, c)
            av, bv, qv, rv = map(self.number, [a, b, quotient, remainder])
            # MiniZinc div truncates towards zero. This mathematical relation
            # avoids both native execution and Python's different // semantics.
            absolute_b = f"Vec.absolute ({bv})"
            result = conjunction(
                [
                    f"{bv} != 0",
                    f"{av} = ({bv} * {qv}) + {rv}",
                    f"{rv} < ({absolute_b})",
                    f"(0 - ({absolute_b})) < {rv}",
                    f"({av} >= 0 && {rv} >= 0) || ({av} <= 0 && {rv} <= 0)",
                ]
            )
        elif operation == "bool2int":
            result = f"{self.number(args[1])} = {indicator(self.boolean(args[0]))}"
        elif operation in ("bool_eq", "bool_ne", "bool_not"):
            symbol = "=" if operation == "bool_eq" else "!="
            result = f"{self.boolean(args[0])} {symbol} {self.boolean(args[1])}"
        elif operation == "bool_xor":
            result = f"({self.boolean(args[0])} != {self.boolean(args[1])}) = {self.boolean(args[2])}"
        elif operation == "bool_clause":
            positive, negative = args
            result = disjunction([self.boolean(v) for v in positive] + [f"{self.boolean(v)} = false" for v in negative])
        elif operation in ("array_bool_and", "array_bool_or"):
            values, target = args
            combine = conjunction if operation == "array_bool_and" else disjunction
            result = f"{combine([self.boolean(v) for v in values])} = {self.boolean(target)}"
        elif operation in (
            "array_int_element",
            "array_var_int_element",
            "array_bool_element",
            "array_float_element",
            "array_var_float_element",
        ):
            index, values, target = args
            at = self.number(index)
            encode = self.boolean if operation == "array_bool_element" else self.number
            # FlatZinc's arrays are one-based. Explicit bounds make the
            # disjunction exact, including constant/out-of-range indices.
            result = disjunction(
                [f"{at} = {i} && {encode(target)} = {encode(value)}" for i, value in enumerate(values, 1)]
            )
        elif operation == "set_in":
            value, allowed = args
            result = disjunction(
                [
                    f"{self.number(value)} = {self.number(item)} && {self.member(allowed, item)}"
                    for item in sorted(self.universe(allowed))
                ]
            )
        elif operation == "set_card":
            value, cardinality = args
            result = f"{total([indicator(self.member(value, item)) for item in sorted(self.universe(value))])} = {self.number(cardinality)}"
        elif operation in ("set_eq", "set_ne"):
            result = self.set_equal(*args)
            if operation == "set_ne":
                result = f"({result}) = false"
        elif operation in ("set_le", "set_lt"):
            left, right = args
            universe = sorted(self.universe(left) | self.universe(right))
            a = self.model.sequence([self.member(left, item) for item in universe], "Bool")
            b = self.model.sequence([self.member(right, item) for item in universe], "Bool")
            result = f"Vec.setLexLe ({a}) ({b})"
            if operation == "set_lt":
                result = f"({result}) && (({self.set_equal(left, right)}) = false)"
        elif operation in ("set_intersect", "set_union", "set_diff"):
            left, right, target = args
            universe = self.universe(left) | self.universe(right) | self.universe(target)
            symbol = "||" if operation == "set_union" else "&&"
            terms = []
            for item in sorted(universe):
                a, b, c = self.member(left, item), self.member(right, item), self.member(target, item)
                if operation == "set_diff":
                    b = f"({b} = false)"
                terms.append(f"({a} {symbol} {b}) = {c}")
            result = conjunction(terms)
        elif operation in ("array_set_element", "array_var_set_element"):
            index, values, target = args
            result = disjunction(
                [
                    f"{self.number(index)} = {i} && ({self.set_equal(value, target)})"
                    for i, value in enumerate(values, 1)
                ]
            )
        else:
            raise Unsupported(f"constraint {operation}")
        if suffix == "reif":
            return f"({result}) = {self.boolean(reification)}"
        if suffix == "imp":
            return f"({self.boolean(reification)} = false) || ({result})"
        return result

    def translate(self) -> Model:
        for statement in self.statements:
            if statement.startswith("predicate "):
                continue
            if statement.startswith("constraint "):
                head = re.match(r"constraint\s+(\w+)\((.*)\)(?:\s*::.*)?$", statement, re.S)
                if not head:
                    raise Unsupported(f"constraint syntax {statement[:100]}")
                # Annotations contain parentheses too; split at :: first.
                call = statement.split("::", 1)[0].strip()
                matched = re.fullmatch(r"constraint\s+(\w+)\((.*)\)", call, re.S)
                if not matched:
                    raise Unsupported(f"constraint syntax {call[:100]}")
                arguments = [self.value(v) for v in split_arguments(matched[2])]
                self.constraints.append(self.relation(matched[1], arguments))
            elif statement.startswith("solve "):
                match = re.search(r"\b(satisfy|minimize|maximize)\b\s*(\w+)?$", statement)
                if not match:
                    raise Unsupported("solve expression")
                self.direction = match[1]
                self.target = self.value(match[2]) if match[2] else None
            elif statement.startswith("array "):
                matched = re.fullmatch(r"array\s*\[[^\]]+\]\s+of\s+[^:]+:\s*(\w+)(.*)", statement, re.S)
                if not matched or "=" not in matched[2]:
                    raise Unsupported("uninitialized array")
                self.values[matched[1]] = self.value(matched[2].split("=", 1)[1])
            elif statement.startswith("var "):
                matched = re.fullmatch(r"var\s+([^:]+):\s*(\w+)(.*)", statement, re.S)
                if not matched:
                    raise Unsupported("variable declaration")
                domain, identifier, tail = matched.groups()
                domain = domain.strip()
                if domain.startswith("set of "):
                    universe = self.value(domain[7:])
                    if not isinstance(universe, frozenset):
                        raise Unsupported("non-finite set domain")
                    members = {}
                    for item in sorted(universe):
                        name = f"decision{len(self.model.variables)}"
                        self.model.variables[name] = [0, 1]
                        self.model.value_types[name] = "Bool"
                        members[item] = Variable(name, 0, 1, True)
                    value = SetVariable(members)
                    self.values[identifier] = value
                    if "=" in tail:
                        self.constraints.append(self.set_equal(value, self.value(tail.split("=", 1)[1])))
                    continue
                boolean = domain == "bool"
                floating = bool(re.fullmatch(r"-?\d+\.\d+(?:[Ee][+-]?\d+)?\.\.-?\d+\.\d+(?:[Ee][+-]?\d+)?", domain))
                lower: int | float
                upper: int | float
                if boolean:
                    lower, upper = 0, 1
                elif interval := re.fullmatch(r"(-?\d+)\.\.(-?\d+)", domain):
                    lower, upper = int(interval[1]), int(interval[2])
                elif floating:
                    lower, upper = map(float, domain.split(".."))
                elif domain.startswith("{"):
                    allowed = sorted(self.value(domain))
                    if not allowed:
                        raise Unsupported("empty variable domain")
                    lower, upper = allowed[0], allowed[-1]
                else:
                    raise Unsupported(f"variable domain {domain}")
                # Identifiers from the compiler remain in the provenance map;
                # generated Aeon identifiers are short, valid, and deterministic.
                name = f"decision{len(self.model.variables)}"
                variable = Variable(name, lower, upper, boolean, floating)
                self.values[identifier] = variable
                self.model.variables[name] = [lower, upper]
                if boolean:
                    self.model.value_types[name] = "Bool"
                if floating:
                    self.model.value_types[name] = "Float"
                if domain.startswith("{"):
                    self.constraints.append(self.relation("set_in", [variable, frozenset(allowed)]))
                if "=" in tail:
                    alias = self.value(tail.split("=", 1)[1])
                    op = "bool_eq" if boolean else "float_eq" if floating else "int_eq"
                    self.constraints.append(self.relation(op, [variable, alias]))
            else:
                matched = re.fullmatch(r"(?:int|float|bool|set of int):\s*(\w+)\s*=\s*(.+)", statement, re.S)
                if not matched:
                    raise Unsupported(f"statement {statement[:100]}")
                self.values[matched[1]] = self.value(matched[2])
        if not self.model.variables:
            raise Unsupported("no decision variables; needs an algorithmic port")
        self.model.constraints = self.constraints or ["true"]
        if self.direction != "satisfy":
            if not isinstance(self.target, Variable) or self.target.boolean:
                raise Unsupported("non-integer optimization objective")
            if self.target.floating:
                self.model.score_type = "Float"
            if self.direction == "minimize":
                self.model.objective = f"{self.target.name} - {self.number(self.target.lower)}"
            else:
                self.model.objective = f"{self.number(self.target.upper)} - {self.target.name}"
            self.model.goal = f"{self.direction.capitalize()} upstream objective within its declared domain."
            self.model.optimum = None
        self.model.data = {
            "flatzinc_identifiers": {
                key: value.name for key, value in self.values.items() if isinstance(value, Variable)
            },
            "set_identifiers": {
                key: {str(item): member.name for item, member in value.members.items()}
                for key, value in self.values.items()
                if isinstance(value, SetVariable)
            },
            "direction": self.direction,
            "objective_identifier": self.target.name if isinstance(self.target, Variable) else None,
        }
        return self.model


def import_models(
    cache: Path, catalogue: Path, results: Path, destination: Path, domain_cache: Path | None = None
) -> dict[str, int]:
    data = json.loads(catalogue.read_text())
    entries = {entry["id"]: entry for entry in data["models"]}
    compiled = json.loads(results.read_text())
    destination.mkdir(parents=True, exist_ok=True)
    if domain_cache is not None:
        domain_cache.mkdir(parents=True, exist_ok=True)
    counts = {"translated": 0, "unsupported": 0, "already_implemented": 0}
    for result in compiled:
        entry = entries[result["anchor"]]
        if entry["status"] == "implemented" or entry.get("porting_method") == "algorithmic":
            counts["already_implemented"] += 1
            continue
        if not result.get("compiled"):
            entry["preparation_error"] = result.get("error", "source compilation failed")
            continue
        text = (cache / (result["anchor"] + ".fzn")).read_text()
        try:
            if domain_cache is None:
                model = Translator(result["name"], text).translate()
            else:
                key = hashlib.sha256(text.encode()).hexdigest()
                inferred = domain_cache / (key + ".fzn")
                if not inferred.exists():
                    inferred.write_text(infer_domains(text, split_arguments))
                model = Translator(result["name"], inferred.read_text(), infer_bounds=False).translate()
        except Unsupported as error:
            entry["porting_error"] = str(error)
            counts["unsupported"] += 1
            continue
        source_url = f"https://github.com/hakank/hakank/blob/{data['upstream_commit']}/{result['source']}"
        model.instance = "explicit prepared parameters " + json.dumps(result.get("parameters", {}), sort_keys=True)
        rendered = model.render({"source_url": source_url})
        file = destination / (entry["id"] + ".ae")
        file.write_text(rendered, encoding="utf-8")
        entry.update(
            status="translated",
            aeon_file=str(file.relative_to(catalogue.parent)),
            compiler_version="2.9.4",
            parameters=result.get("parameters", {}),
            data_files=result.get("data_files", []),
            flatzinc_sha256=hashlib.sha256(re.sub(r"%[^\n]*", "", text).encode()).hexdigest(),
            variables=model.variables,
            variable_map=model.data["flatzinc_identifiers"],
            set_map=model.data["set_identifiers"],
            value_types=model.value_types,
            float_grid=0.001 if "Float" in model.value_types.values() else None,
            direction=model.data["direction"],
            objective_identifier=model.data["objective_identifier"],
        )
        entry.pop("porting_error", None)
        entry.pop("preparation_error", None)
        counts["translated"] += 1
    catalogue.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cache", required=True, type=Path)
    parser.add_argument("--catalogue", required=True, type=Path)
    parser.add_argument("--results", required=True, type=Path)
    parser.add_argument("--destination", required=True, type=Path)
    parser.add_argument("--domain-cache", type=Path)
    args = parser.parse_args()
    print(import_models(args.cache, args.catalogue, args.results, args.destination, args.domain_cache))


if __name__ == "__main__":
    main()
