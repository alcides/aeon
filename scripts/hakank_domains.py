"""Conservatively infer finite domains for compiler-generated auxiliaries.

Only unconditional constraints participate. Bounds must follow from the
source equations; this pass never substitutes an arbitrary search cutoff.
"""

from fractions import Fraction
from math import ceil, floor
import re


def infer_domains(text, split_arguments):
    if not re.search(r"var\s+(?:int|float):", text):
        return text
    values = {}
    bounds = {}
    kinds = {}
    constraints = []
    statements = [s.strip() for s in re.sub(r"%[^\n]*", "", text).split(";") if s.strip()]

    def value(source):
        source = source.strip()
        if source in values:
            return values[source]
        if source.startswith("["):
            return [value(s) for s in split_arguments(source[1:-1])]
        if source in ("true", "false"):
            return int(source == "true")
        if re.fullmatch(r"-?\d+(?:\.\d+)?(?:[Ee][+-]?\d+)?", source):
            return Fraction(source)
        return source

    def interval(item):
        return (item, item) if isinstance(item, (int, Fraction)) else bounds.get(item, (None, None))

    def narrow(item, lower, upper):
        if not isinstance(item, str) or item not in bounds:
            return False
        old_lower, old_upper = bounds[item]
        if kinds[item] == "int":
            lower = ceil(lower) if lower is not None else None
            upper = floor(upper) if upper is not None else None
        new_lower = (
            max(old_lower, lower)
            if old_lower is not None and lower is not None
            else old_lower
            if lower is None
            else lower
        )
        new_upper = (
            min(old_upper, upper)
            if old_upper is not None and upper is not None
            else old_upper
            if upper is None
            else upper
        )
        bounds[item] = new_lower, new_upper
        return bounds[item] != (old_lower, old_upper)

    for statement in statements:
        if match := re.match(r"var\s+([^:]+):\s*(\w+)(.*)", statement, re.S):
            domain, name, tail = match.groups()
            domain = domain.strip()
            if domain.startswith("set of"):
                continue
            kinds[name] = "float" if domain == "float" or "." in domain.replace("..", "") else "int"
            if domain in ("int", "float"):
                bounds[name] = None, None
            elif domain == "bool":
                bounds[name] = 0, 1
            elif ".." in domain:
                lower, upper = domain.split("..")
                bounds[name] = Fraction(lower), Fraction(upper)
            elif domain.startswith("{"):
                members = [Fraction(s) for s in split_arguments(domain[1:-1])]
                bounds[name] = min(members), max(members)
            else:
                continue
            values[name] = name
            if "=" in tail:
                constraints.append(("int_eq", [name, value(tail.split("=", 1)[1])]))
        elif statement.startswith("array ") and "=" in statement:
            match = re.match(r"array\s*\[[^\]]+\]\s+of\s+[^:]+:\s*(\w+)(.*)", statement, re.S)
            if match:
                values[match[1]] = value(match[2].split("=", 1)[1])
        elif match := re.fullmatch(r"(?:int|float|bool):\s*(\w+)\s*=\s*(.+)", statement, re.S):
            values[match[1]] = value(match[2])
        elif statement.startswith("constraint "):
            match = re.fullmatch(r"constraint\s+(\w+)\((.*)\)", statement.split("::", 1)[0].strip(), re.S)
            if match:
                constraints.append((match[1], [value(s) for s in split_arguments(match[2])]))

    for _ in range(100):
        changed = False
        for operation, arguments in constraints:
            if operation.endswith(("_reif", "_imp")):
                continue
            if operation in ("int_eq", "float_eq", "int2float", "bool2int"):
                a, b = arguments
                changed |= narrow(a, *interval(b))
                changed |= narrow(b, *interval(a))
            elif operation in ("int_le", "float_le"):
                a, b = arguments
                changed |= narrow(a, None, interval(b)[1])
                changed |= narrow(b, interval(a)[0], None)
            elif operation in ("int_lin_eq", "int_lin_le", "float_lin_eq", "float_lin_le"):
                coefficients, variables, target = arguments
                terms = {}
                constant = Fraction(0)
                for coefficient, item in [*zip(coefficients, variables), (-1, target)]:
                    if isinstance(item, str):
                        terms[item] = terms.get(item, 0) + coefficient
                    elif isinstance(item, (int, Fraction)):
                        constant += coefficient * item
                terms = {item: coefficient for item, coefficient in terms.items() if coefficient}
                for item, coefficient in terms.items():
                    lower = upper = constant
                    for other, multiplier in terms.items():
                        if other == item:
                            continue
                        lo, hi = interval(other)
                        if multiplier < 0:
                            lo, hi = hi, lo
                        lower = lower + multiplier * lo if lower is not None and lo is not None else None
                        upper = upper + multiplier * hi if upper is not None and hi is not None else None
                    lo = -upper / coefficient if upper is not None else None
                    hi = -lower / coefficient if lower is not None else None
                    if coefficient < 0:
                        lo, hi = hi, lo
                    if operation.endswith("_le"):
                        lo, hi = (None, hi) if coefficient > 0 else (lo, None)
                    changed |= narrow(item, lo, hi)
            elif operation in ("int_times", "float_times"):
                a, b, target = arguments
                endpoints = [*interval(a), *interval(b)]
                if all(point is not None for point in endpoints):
                    products = [x * y for x in interval(a) for y in interval(b)]
                    changed |= narrow(target, min(products), max(products))
            elif operation in ("array_int_element", "array_var_int_element", "array_float_element"):
                _, array, target = arguments
                endpoints = [interval(item) for item in array]
                if endpoints and all(lo is not None and hi is not None for lo, hi in endpoints):
                    changed |= narrow(target, min(lo for lo, hi in endpoints), max(hi for lo, hi in endpoints))
            elif operation in ("int_abs", "float_abs"):
                argument, target = arguments
                lo, hi = interval(argument)
                changed |= narrow(target, 0, max(abs(lo), abs(hi)) if lo is not None and hi is not None else None)
                hi = interval(target)[1]
                if hi is not None:
                    changed |= narrow(argument, -hi, hi)
        if not changed:
            break

    def replace(match):
        kind, name = match.groups()
        lower, upper = bounds.get(name, (None, None))
        if lower is None or upper is None or lower > upper:
            return match[0]
        encode = (lambda v: str(int(v))) if kind == "int" else (lambda v: str(float(v)))
        return f"var {encode(lower)}..{encode(upper)}: {name}"

    return re.sub(r"var\s+(int|float):\s*(\w+)", replace, text)
