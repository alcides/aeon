"""Port Clause2Inv's three invariant obligations to sampled Aeon properties.

The original SMT templates remain the authoritative universal specification.
No claim of SMT verification follows from passing these property tests.
"""

import re
from fractions import Fraction

from .common import Group, identifier, sexprs


def has_real(node):
    if isinstance(node, str) and re.fullmatch(r"-?\d+\.\d+", node):
        return True
    if isinstance(node, Group) and node.items[0] in ("div", "mod"):
        return False
    return isinstance(node, Group) and (node.items[0] == "/" or any(has_real(x) for x in node.items[1:]))


def rational_expression(node):
    if isinstance(node, str) and re.fullmatch(r"-?\d+\.\d+", node):
        value = Fraction(node)
        return f"(rationalDiv (rational {expression(value.numerator)}) (rational {value.denominator}))"
    if not isinstance(node, Group) or node.items[0] in ("div", "mod"):
        return f"(rational {expression(node)})"
    op, *children = node.items
    args = [rational_expression(x) for x in children]
    if op == "-" and len(args) == 1:
        args.insert(0, "(rational 0)")
    function = {"+": "rationalAdd", "-": "rationalSub", "*": "rationalMul", "/": "rationalDiv"}[op]
    result = args[0]
    for arg in args[1:]:
        result = f"({function} {result} {arg})"
    return result


def expression(node):
    if isinstance(node, int):
        return str(node) if node >= 0 else f"(0 - {-node})"
    if isinstance(node, str):
        return node if node in ("true", "false") else identifier(node)
    op, *children = node.items
    if op in ("=", "<", ">", "<=", ">=") and any(has_real(c) for c in children):
        args = [rational_expression(x) for x in children]
        function = {"=": "rationalEq", "<": "rationalLt", ">": "rationalGt", "<=": "rationalLe", ">=": "rationalGe"}[op]
        return "(" + " && ".join(f"({function} {a} {b})" for a, b in zip(args, args[1:])) + ")"
    args = [expression(x) for x in children]
    if op == "not":
        return f"(!{args[0]})"
    if op == "=>":
        return f"((!{args[0]}) || {args[1]})"
    if op == "ite":
        return f"(if {args[0]} then {args[1]} else {args[2]})"
    if op in ("and", "or", "+", "*", "-"):
        operator = {"and": "&&", "or": "||"}.get(op, op)
        if not args:
            return {"and": "true", "or": "false", "+": "0", "*": "1"}[op]
        if op == "-" and len(args) == 1:
            return f"(0 - {args[0]})"
        return "(" + f" {operator} ".join(args) + ")"
    if op in ("=", "<", ">", "<=", ">="):
        return "(" + " && ".join(f"({a} {op} {b})" for a, b in zip(args, args[1:])) + ")"
    if op in ("div", "mod", "/"):
        # The source tool uses Z3's implicit Real -> Int coercion for integer
        # operators (notably mod (/ count 2) 2): to_int is floor, not truncation.
        if op in ("div", "mod"):
            args = [f"(rationalFloor {rational_expression(x)})" if has_real(x) else expression(x) for x in children]
        return f"(smt_{ {'div': 'div', 'mod': 'mod', '/': 'real_div'}[op] } {' '.join(args)})"
    if op in ("inv-f", "pre-f", "trans-f", "post-f"):
        return f"({identifier(op)} {' '.join(args)})"
    raise ValueError(f"Unknown SMT operator: {op}")


def clause2inv(corpus):
    root = corpus.source_root / "clause2inv/combinator/Benchmarks"
    for suite, directory in [("linear", "Linear/c_smt2"), ("nonlinear", "NL/c_smt")]:
        for path in sorted((root / directory).iterdir()):
            if path.name == "NL51.c_smt":
                # Not one of the paper's 50 nonlinear tasks: this extra file
                # has erased variable names and incomplete arithmetic terms.
                continue
            text = re.sub(r";[^\n]*", "", path.read_text())
            forms = [x for x in sexprs(text) if isinstance(x, Group)]
            variables = [(x.items[1], x.items[2]) for x in forms if x.items[0] == "declare-const"]
            definitions = [x.items for x in forms if x.items[0] == "define-fun"]
            obligations = [x.items[1] for x in forms if x.items[0] == "assert"]
            assert len(definitions) == 4 and len(obligations) == 3
            code = "# Property testing is sampled; use the upstream SMT template for proofs.\nopen SMTArithmetic\n"
            for _, name, args, result, body in definitions:
                binders = " ".join(f"({identifier(a.items[0])}:{a.items[1]})" for a in args.items)
                rhs = "?invariant" if name == "inv-f" else expression(body)
                code += f"def {identifier(name)} {binders} : {result} := {rhs};\n\n"
            names = ["initiation", "consecution", "safety"]
            binders = " ".join(f"({identifier(n)}:{t})" for n, t in variables)
            for name, obligation in zip(names, obligations, strict=True):
                assert obligation.items[0] == "not"
                code += f"@property(200)\ndef {name} {binders} : Bool := {expression(obligation.items[1])};\n\n"
            corpus.add(
                f"clause2inv/{suite}",
                identifier(path.name),
                path,
                code,
                specification="sampled-invariant-obligations",
                properties=3,
                proof_required=True,
            )
