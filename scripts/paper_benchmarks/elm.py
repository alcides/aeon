"""Translate Smyth's explicitly typed, layout-sensitive sketch language."""

import re
import textwrap

from .common import digest, identifier
from .ml import Emitter, Parser


def clean(source):
    return re.sub(r"--[^\n]*", "", source)


class ElmParser(Parser):
    def __init__(self, source):
        self.tokens = re.findall(r"\?\?|->|[A-Za-z_][A-Za-z_0-9']*|\d+|[^\s]", source) + ["EOF"]
        self.pos = 0

    def typ(self):
        if self.accept("forall"):
            variable = self.pop()
            self.pop(".")
            return ("forall", variable, self.typ())

        def atom():
            if self.accept("("):
                if self.accept(")"):
                    return "unit"
                items = [self.typ()]
                while self.accept(","):
                    items.append(self.typ())
                self.pop(")")
                return items[0] if len(items) == 1 else ("prod", *items)
            return self.pop()

        first = atom()
        params = []
        while self.peek() == "(" or re.fullmatch(r"[A-Za-z_][\w']*", self.peek()) and self.peek() != "EOF":
            params.append(atom())
        result = ("appT", first, *params) if params else first
        return ("arrow", result, self.typ()) if self.accept("->") else result

    def starts_atom(self):
        return self.peek() in ("[", "#", "??") or super().starts_atom()

    def atom(self):
        if self.accept("??"):
            return ("hole",)
        if self.accept("#"):
            self.pop()  # tuple arity, checked by the source type
            self.pop(".")
            index = int(self.pop()) - 1
            return ("proj", self.atom(), index)
        if self.accept("["):
            items = []
            if self.peek() != "]":
                items.append(self.expr())
                while self.accept(","):
                    items.append(self.expr())
            self.pop("]")
            types = self.type_arguments() if self.peek() == "<" else []
            result = ("typed_ctor", "Nil", types, ("unit",)) if types else ("ctor", "Nil", ("unit",))
            for item in reversed(items):
                result = (
                    ("typed_ctor", "Cons", types, ("tuple", item, result))
                    if types
                    else ("ctor", "Cons", ("tuple", item, result))
                )
            return result
        if self.peek()[:1].isupper() and self.tokens[self.pos + 1] == "<":
            ctor = self.pop()
            types = self.type_arguments()
            payload = self.atom() if self.starts_atom() else ("unit",)
            return ("typed_ctor", ctor, types, payload)
        result = super().atom()
        if self.peek() == "<":
            result = ("inst", result, self.type_arguments())
        return result

    def type_arguments(self):
        self.pop("<")
        args = [self.typ()]
        while self.accept(","):
            args.append(self.typ())
        self.pop(">")
        return args


def parse_type(source):
    parser = ElmParser(source)
    typ = parser.typ()
    parser.pop("EOF")
    return typ


def expression(source):
    source = textwrap.dedent(source).strip()
    lines = source.splitlines()
    first = lines[0].strip()
    if first.startswith("case "):
        assert first.endswith(" of")
        scrutinee = expression(first[5:-3])
        candidates = [(i, len(line) - len(line.lstrip())) for i, line in enumerate(lines[1:], 1) if "->" in line]
        indent = min(n for _, n in candidates)
        indices = [i for i, n in candidates if n == indent] + [len(lines)]
        branches = []
        for start, end in zip(indices, indices[1:]):
            pat, rhs = lines[start].strip().split("->", 1)
            parser = ElmParser(pat)
            pattern = parser.pattern()
            parser.pop("EOF")
            body = "\n".join([" " * (indent + 2) + rhs.strip(), *lines[start + 1 : end]])
            branches.append((pattern, expression(textwrap.dedent(body).strip())))
        return ("match", scrutinee, branches)
    if first == "let":
        stop = next(i for i, line in enumerate(lines) if line.strip() == "in" and not line.startswith(" "))
        defs = declarations(textwrap.dedent("\n".join(lines[1:stop])))
        result = expression(textwrap.dedent("\n".join(lines[stop + 1 :])))
        for tag, name, typ, body in reversed(defs):
            assert tag == "let"
            result = ("letrec", name, typ, body, result)
        return result
    parser = ElmParser(source)
    result = parser.expr()
    parser.pop("EOF")
    return result


def declarations(source):
    source = clean(source)
    starts = [m.start() for m in re.finditer(r"(?m)^(?:type\s+|[A-Za-z_][\w']*\s*:)", source)] + [len(source)]
    result = []
    for start, end in zip(starts, starts[1:]):
        block = source[start:end].strip()
        if block.startswith("type "):
            heading, body = block.split("=", 1)
            name, *parameters = heading[5:].split()
            ctors = []
            for item in body.split("|"):
                ctor, payload = item.strip().split(None, 1)
                ctors.append((ctor, parse_type(payload)))
            result.append(("type", name, parameters, ctors))
        else:
            signature, body = block.split("\n", 1)
            name, typ = signature.split(":", 1)
            name = name.strip()
            typ = parse_type(typ.strip())
            lhs, rhs = body.split("=", 1)
            lhs = re.sub(r"<[^>]+>", "", lhs)
            bound = lhs.split()
            assert bound[0] == name
            concrete = typ
            while isinstance(concrete, tuple) and concrete[0] == "forall":
                concrete = concrete[2]
            args = []
            for argument in bound[1:]:
                assert concrete[0] == "arrow"
                args.append((argument, concrete[1]))
                concrete = concrete[2]
            term = expression(textwrap.dedent(rhs))
            for argument, t in reversed(args):
                term = ("lam", argument, t, term)
            result.append(("let", name, typ, term))
    return result


def render_declarations(decls, emitter):
    code = []
    for tag, name, info, body in decls:
        if tag == "type":
            emitter.type_variables.update(info)
            owner = ("appT", name, *info) if info else name
            code.append(f"inductive T_{name} {' '.join(info)}")
            for ctor, payload in body:
                emitter.ctors[ctor] = (payload, owner)
                binders = "" if payload == "unit" else f"(payload:{emitter.typ(payload)})"
                code.append(f"| C_{ctor} {binders} : {emitter.typ(owner)}")
        else:
            poly = info
            while isinstance(poly, tuple) and poly[0] == "forall":
                emitter.type_variables.add(poly[1])
                poly = poly[2]
            emitter.env[name] = info
            rendered = emitter.expr(body, expected=poly)
            poly = info
            variables = []
            while isinstance(poly, tuple) and poly[0] == "forall":
                variables.append(poly[1])
                poly = poly[2]
            for variable in reversed(variables):
                rendered = f"(Λ {variable}:B => {rendered})"
            code.append(f"def {identifier(name)} : {emitter.typ(info)} := {rendered};\n")
    return "\n".join(code) + "\n"


def translate(sketch, examples):
    declarations_ast = declarations(sketch)
    emitter = Emitter()
    emitter.monomorphic_products = False
    source = render_declarations(declarations_ast, emitter)
    parser = ElmParser(clean(examples))
    specify = parser.pop()
    assert specify.startswith("specifyFunction")
    arity = int(specify[len("specifyFunction") :] or "1")
    target = parser.atom()
    parser.pop("[")
    rows = []
    while parser.peek() != "]":
        row = parser.atom()
        assert row[0] == "tuple" and len(row) == arity + 2, row
        args = row[1:-1]
        out = row[-1]
        rows.append(f"@example({emitter.expr(target)} {' '.join(emitter.expr(x) for x in args)} = {emitter.expr(out)})")
        if not parser.accept(","):
            break
    parser.pop("]")
    parser.pop("EOF")
    name = target[1] if target[0] == "var" else target[1][1]
    source = source.replace(f"def {identifier(name)} :", "\n".join(rows) + f"\ndef {identifier(name)} :", 1)
    return emitter.products() + source, len(rows)


def smyth(corpus):
    root = corpus.source_root / "smyth/suites"
    for suite in sorted(root.iterdir()):
        if not suite.is_dir():
            continue
        for example in sorted((suite / "examples").glob("*.elm")):
            if example.name.startswith("."):
                continue
            sketch = suite / "sketches" / example.name
            if suite.name == "no-sketch":
                sketch = root / "myth/sketches" / example.name
            if not sketch.exists() and sketch.with_name("." + sketch.name).exists():
                sketch = sketch.with_name("." + sketch.name)
            reconstructed = not sketch.exists()
            if not sketch.exists():
                source = reconstructed_sketch(example.stem, suite.name.startswith("poly-"))
                sketch = example
            else:
                source = sketch.read_text()
            # A disabled upstream polymorphic postorder sketch hardcodes Nat
            # in Tree a; its public examples instantiate only Nat. Use the same
            # generic Tree declaration as the active traversal sketches.
            repaired = "| Node (Tree a, Nat, Tree a)" in source
            source = source.replace("| Node (Tree a, Nat, Tree a)", "| Node (Tree a, a, Tree a)")
            code, count = translate(source, example.read_text())
            corpus.add(
                f"smyth/{suite.name}",
                example.stem,
                example,
                code,
                specification="examples-and-sketch",
                examples=count,
                sketch=sketch.relative_to(corpus.source_root).as_posix(),
                sketch_sha256=digest(sketch),
                reconstructed_whole_function_hole=reconstructed,
                repaired_tree_parameter=repaired,
            )


def reconstructed_sketch(task, polymorphic):
    """Recover missing whole-function sketches from published concrete examples."""
    base = "type Nat\n  = Z ()\n  | S Nat\n\ntype Boolean\n  = F ()\n  | T ()\n\n"
    if polymorphic:
        base += "type List a\n  = Nil ()\n  | Cons (a, List a)\n\ntype Tree a\n  = Leaf ()\n  | Node (Tree a, a, Tree a)\n\n"
        signatures = {
            "tree_binsert": ("treeBInsert", "forall a . Tree a -> a -> Tree a", "<a> tree value"),
            "tree_nodes_at_level": ("treeNodesAtLevel", "forall a . Tree a -> Nat -> Nat", "<a> tree level"),
            "tree_postorder": ("treePostorder", "forall a . Tree a -> List a", "<a> tree"),
            "list_pairwise_swap": ("listPairwiseSwap", "forall a . List a -> List a", "<a> xs"),
        }
    else:
        base += "type NatTree\n  = Leaf ()\n  | Node (NatTree, Nat, NatTree)\n\n"
        signatures = {"tree_binsert": ("treeBInsert", "NatTree -> Nat -> NatTree", "tree value")}
    name, typ, args = signatures[task]
    return base + f"{name} : {typ}\n{name} {args} =\n  ??\n"
