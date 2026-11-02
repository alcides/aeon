"""Translate the explicitly typed ML artifact language used by Burst and Trio.

Products and constructor payloads retain their source structure. In particular,
natural numbers remain Peano naturals, rather than silently becoming integers.
"""

from __future__ import annotations

import re

from .common import identifier


RESERVED = {"type", "let", "fun", "fix", "match", "with", "of", "synth", "satisfying", "equiv", "include"}


def read_source(path):
    source = path.read_text()
    if path.name == "nat_fac_tailcall.mls" and source.startswith("nat_fac_tailcall.mls\n"):
        # The JFP archive accidentally includes its filename as the first line.
        source = source.split("\n", 1)[1]
        source = source.replace("fun (acc:nat)\n", "fun (acc:nat) ->\n")
    # The artifacts use nested OCaml comments.
    while "(*" in source:
        changed = re.sub(r"\(\*(?:(?!\(\*|\*\)).)*\*\)", " ", source, flags=re.S)
        if changed == source:
            raise ValueError(f"Unbalanced comment in {path}")
        source = changed

    def include(match):
        name = match[1]
        choices = [path.parent / name, path.parent.parent / name, path.parent.parent / "decls" / name]
        found = [p for p in choices if p.exists()]
        if not found:
            found = list(path.parent.parent.rglob(name))
        if not found:
            raise ValueError(f"Missing include {name}")
        return read_source(found[0])

    return re.sub(r'include\s+"([^"]+)"', include, source)


class Parser:
    def __init__(self, source):
        self.tokens = re.findall(r"->|==|!=|;;|[A-Za-z_][A-Za-z_0-9']*|\d+|[^\s]", source) + ["EOF"]
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos]

    def pop(self, expected=None):
        value = self.peek()
        if expected is not None and value != expected:
            raise ValueError(
                f"Expected {expected}, found {value}; near {self.tokens[max(0, self.pos - 5) : self.pos + 8]}"
            )
        self.pos += 1
        return value

    def accept(self, token):
        if self.peek() == token:
            self.pop()
            return True
        return False

    def typ(self):
        def atom():
            if self.accept("("):
                t = self.typ()
                self.pop(")")
                return t
            return self.pop()

        ts = [atom()]
        while self.accept("*"):
            ts.append(atom())
        t = ts[0] if len(ts) == 1 else ("prod", *ts)
        return ("arrow", t, self.typ()) if self.accept("->") else t

    def param(self):
        self.pop("(")
        name = self.pop()
        self.pop(":")
        typ = self.typ()
        self.pop(")")
        return name, typ

    def declarations(self):
        result = []
        while self.peek() in ("type", "let"):
            tag = self.pop()
            name = self.pop()
            self.pop("=")
            if tag == "type":
                constructors = []
                while self.accept("|"):
                    ctor = self.pop()
                    payload = self.typ() if self.accept("of") else "unit"
                    constructors.append((ctor, payload))
                if not constructors:
                    raise ValueError("Expected algebraic type")
                result.append(("type", name, constructors))
            else:
                result.append(("let", name, self.expr()))
                # GuideSyn/tree_bonus omits the final declaration separator.
                if self.peek() != "synth":
                    self.pop(";;")
        return result

    def starts_atom(self):
        t = self.peek()
        return t == "(" or t.isdigit() or (re.fullmatch(r"[A-Za-z_][\w']*", t) and t not in RESERVED and t != "EOF")

    def expr(self):
        if self.accept("fun"):
            name, typ = self.param()
            self.pop("->")
            return ("lam", name, typ, self.expr())
        if self.accept("fix"):
            name, typ = self.param()
            self.pop("=")
            return ("fix", name, typ, self.expr())
        if self.accept("match"):
            scrutinee = self.expr()
            self.pop("with")
            branches = []
            while self.accept("|"):
                pat = self.pattern()
                self.pop("->")
                branches.append((pat, self.expr()))
            return ("match", scrutinee, branches)
        result = self.atom()
        while self.starts_atom():
            result = ("app", result, self.atom())
        if self.peek() in ("==", "!="):
            op = self.pop()
            result = ("eq", op, result, self.expr())
        return result

    def atom(self):
        if self.accept("("):
            if self.accept(")"):
                result = ("unit",)
            else:
                items = [self.expr()]
                while self.accept(","):
                    items.append(self.expr())
                self.pop(")")
                result = items[0] if len(items) == 1 else ("tuple", *items)
        else:
            t = self.pop()
            if t.isdigit():
                result = ("nat", int(t))
            elif t[:1].isupper():
                payload = self.atom() if self.starts_atom() else ("unit",)
                result = ("ctor", t, payload)
            elif re.fullmatch(r"[a-z_][\w']*", t) and t not in RESERVED:
                result = ("var", t)
            else:
                raise ValueError(f"Unexpected expression token {t} at {self.tokens[self.pos - 8 : self.pos + 8]}")
        while self.accept("."):
            result = ("proj", result, int(self.pop()))
        return result

    def pattern(self):
        if self.accept("("):
            if self.accept(")"):
                return ("unit",)
            items = [self.pattern()]
            while self.accept(","):
                items.append(self.pattern())
            self.pop(")")
            return items[0] if len(items) == 1 else ("tuple", *items)
        token = self.pop()
        if token == "_":
            return ("wild",)
        if token[:1].isupper():
            payload = self.pattern() if self.peek() not in ("->", ",", ")") else ("wild",)
            return ("ctor", token, payload)
        return ("var", token)

    def problem(self):
        before = self.declarations()
        self.pop("synth")
        target = self.typ()
        self.pop("satisfying")
        after = self.declarations()
        if self.accept("equiv"):
            specification = ("reference", self.expr())
        elif self.peek() == "[":
            examples = []
            while self.accept("["):
                args = []
                if self.peek() != "]":
                    args.append(self.expr())
                    while self.accept(","):
                        args.append(self.expr())
                self.pop("]")
                self.pop("->")
                examples.append((args, self.expr()))
                if not self.accept(","):
                    break
            specification = ("examples", examples)
        else:
            specification = ("logical", self.expr())
        self.pop("EOF")
        return before, target, after, specification


class Emitter:
    def __init__(self):
        self.ctors = {}
        self.env = {}
        self.product_arities = set()
        self.counter = 0
        self.type_variables = set()
        self.monomorphic_products = True
        self.product_types = {}
        self.function_choice = None

    def fresh(self):
        self.counter += 1
        return f"part_{self.counter}"

    def typ(self, t):
        if isinstance(t, str):
            if t in self.type_variables:
                return t
            if t == "__Bool":
                return "Bool"
            return "Unit" if t == "unit" else "T_" + identifier(t)
        if t[0] == "arrow":
            return f"(arg:{self.typ(t[1])}) -> {self.typ(t[2])}"
        if t[0] == "appT":
            return f"(T_{t[1]} {' '.join('(' + self.typ(x) + ')' for x in t[2:])})"
        if t[0] == "forall":
            return f"forall {t[1]}:B, {self.typ(t[2])}"
        assert t[0] == "prod"
        if self.monomorphic_products:
            return self.product_name(t)
        self.product_arities.add(len(t) - 1)
        return f"(Product{len(t) - 1} {' '.join('(' + self.typ(x) + ')' for x in t[1:])})"

    def product_name(self, typ):
        if not self.monomorphic_products:
            self.product_arities.add(len(typ) - 1)
            return f"Product{len(typ) - 1}"
        if typ not in self.product_types:
            self.product_types[typ] = f"MonoProduct{len(self.product_types) + 1}"
        return self.product_types[typ]

    def product_constructor(self, typ):
        name = self.product_name(typ)
        return name, "make" + name if self.monomorphic_products else f"product{len(typ) - 1}"

    def infer(self, e, env):
        tag = e[0]
        if tag == "var":
            return env[e[1]]
        if tag == "unit":
            return "unit"
        if tag == "nat":
            return self.ctors["O" if "O" in self.ctors else "Z"][1]
        if tag == "ctor":
            if e[1].startswith("Un_"):
                return self.ctors[e[1][3:]][0]
            return self.ctors[e[1]][1]
        if tag == "typed_ctor":
            owner = self.ctors[e[1]][1]
            return substitute_type(owner, dict(zip(owner[2:], e[2], strict=True)))
        if tag in ("lam", "fix"):
            inner = {**env, e[1]: e[2]}
            return fix_type(e) if tag == "fix" else ("arrow", e[2], self.infer(e[3], inner))
        if tag == "inst":
            typ = self.infer(e[1], env)
            for arg in e[2]:
                assert typ[0] == "forall", typ
                typ = substitute_type(typ[2], {typ[1]: arg})
            return typ
        if tag == "tuple":
            return ("prod", *(self.infer(x, env) for x in e[1:]))
        if tag == "proj":
            return self.infer(e[1], env)[e[2] + 1]
        if tag == "app":
            return self.infer(e[1], env)[2]
        if tag == "eq":
            return "bool" if "True" in self.ctors else "__Bool"
        if tag == "match":
            pat, body = e[2][0]
            return self.infer(body, {**env, **self.bindings(pat, self.infer(e[1], env))})
        raise ValueError(tag)

    def bindings(self, pat, typ):
        if pat[0] == "var":
            return {pat[1]: typ}
        if pat[0] == "ctor":
            payload, _ = self.ctors[pat[1]]
            return self.bindings(pat[2], payload)
        if pat[0] == "tuple":
            result = {}
            for p, t in zip(pat[1:], typ[1:], strict=True):
                result.update(self.bindings(p, t))
            return result
        return {}

    def pattern(self, pat, typ):
        if pat[0] == "wild":
            return "_", []
        if pat[0] == "var":
            return identifier(pat[1]), []
        if pat[0] == "unit":
            return "_", []
        if pat[0] == "ctor":
            payload = self.ctors[pat[1]][0]
            if payload == "unit":
                return "C_" + pat[1], []
            if pat[2][0] in ("var", "wild"):
                binding, _ = self.pattern(pat[2], payload)
                return f"C_{pat[1]} {binding}", []
            temporary = self.fresh()
            return f"C_{pat[1]} {temporary}", [(temporary, pat[2], payload)]
        if pat[0] == "tuple":
            self.product_arities.add(len(pat) - 1)
            names, destructure = [], []
            for p, t in zip(pat[1:], typ[1:], strict=True):
                if p[0] in ("var", "wild"):
                    n, _ = self.pattern(p, t)
                else:
                    n = self.fresh()
                    destructure.append((n, p, t))
                names.append(n)
            return f"product{len(names)} {' '.join(names)}", destructure
        raise ValueError(pat)

    def expr(self, e, env=None, expected=None):
        env = self.env if env is None else env
        while isinstance(expected, tuple) and expected[0] == "forall":
            expected = expected[2]
        tag = e[0]
        if tag == "var":
            return identifier(e[1])
        if tag == "unit":
            return '(native "None")'
        if tag == "nat":
            zero = "O" if "O" in self.ctors else "Z"
            nat_type = self.ctors[zero][1]
            result = f"T_{nat_type}.C_{zero}"
            for _ in range(e[1]):
                result = f"(T_{nat_type}.C_S {result})"
            return result
        if tag == "ctor":
            if e[1].startswith("Un_"):
                temporary = self.fresh()
                return f"(match {self.expr(e[2], env)} with | C_{e[1][3:]} {temporary} => {temporary})"
            payload = self.ctors[e[1]][0]
            owner = self.ctors[e[1]][1]
            name = f"T_{owner if isinstance(owner, str) else owner[1]}.C_{e[1]}"
            return name if payload == "unit" else f"({name} {self.expr(e[2], env)})"
        if tag == "typed_ctor":
            owner = self.ctors[e[1]][1]
            name = f"T_{owner[1]}.C_{e[1]}" + "".join("{" + self.typ(t) + "}" for t in e[2])
            return "(" + name + (" " + self.expr(e[3], env) if self.ctors[e[1]][0] != "unit" else "") + ")"
        if tag == "tuple":
            typ = self.infer(e, env) if self.monomorphic_products else ("prod", *("a" for _ in e[1:]))
            name, ctor = self.product_constructor(typ)
            return f"({name}.{ctor} {' '.join(self.expr(x, env) for x in e[1:])})"
        if tag == "proj":
            typ = self.infer(e[1], env)
            assert typ[0] == "prod"
            name = self.product_name(typ)
            return f"(project{name}_{e[2]} {self.expr(e[1], env)})"
        if tag == "lam":
            result_type = expected[2] if isinstance(expected, tuple) and expected[0] == "arrow" else None
            return f"(fun {identifier(e[1])} => {self.expr(e[3], {**env, e[1]: e[2]}, result_type)})"
        if tag == "inst":
            return "(" + self.expr(e[1], env) + "".join("{" + self.typ(t) + "}" for t in e[2]) + ")"
        if tag == "hole":
            return "?hole" + self.fresh()
        if tag == "letrec":
            _, name, typ, body, result = e
            inner = {**env, name: typ}
            rendered = self.expr(body, inner, typ)
            poly = typ
            variables = []
            while isinstance(poly, tuple) and poly[0] == "forall":
                variables.append(poly[1])
                poly = poly[2]
            for variable in reversed(variables):
                rendered = f"(Λ {variable}:B => {rendered})"
            return f"(let {identifier(name)} : {self.typ(typ)} := {rendered} in {self.expr(result, inner, expected)})"
        if tag == "fix":
            name = identifier(e[1])
            typ = fix_type(e)
            return f"(let {name} : {self.typ(typ)} := {self.expr(e[3], {**env, e[1]: typ}, typ)} in {name})"
        if tag == "app":
            return f"({self.expr(e[1], env)} {self.expr(e[2], env)})"
        if tag == "eq":
            op = "=" if e[1] == "==" else "!="
            typ = self.infer(e[2], env)
            if isinstance(typ, tuple) and typ[0] == "arrow":
                # The artifact compares the first function input syntactically
                # against a named helper. Specialize its finite helper corpus;
                # never pretend runtime/extensional equality is decidable.
                assert self.function_choice is not None and e[3][0] == "var", e
                assert e[2][0] == "proj" and e[2][2] == 0, e
                equal = self.function_choice == e[3][1]
                eq = str(equal if op == "=" else not equal).lower()
            else:
                eq = f"({self.expr(e[2], env)} {op} {self.expr(e[3], env)})"
            return f"(if {eq} then T_bool.C_True else T_bool.C_False)" if "True" in self.ctors else eq
        if tag == "match":
            scrutinee = self.expr(e[1], env)
            typ = self.infer(e[1], env)
            result_type = expected or self.infer(e, env)
            result = "(native \"(_ for _ in ()).throw(ValueError('non-exhaustive source pattern'))\")"
            for pat, body in reversed(e[2]):
                inner = {**env, **self.bindings(pat, typ)}
                rhs = self.expr(body, inner, result_type)
                # A nested pattern may fail at several depths. Share the
                # remaining clauses as a thunk instead of copying the whole
                # decision tree at every failure edge (exponential growth).
                continuation = self.fresh()
                fallback = self.fresh()
                branch = self.pattern_test(pat, scrutinee, typ, rhs, f"(forceBranch {fallback})", result_type)
                result = (
                    f"(let {continuation} : (ignored:Bool) -> {self.typ(result_type)} := "
                    f"(fun delayed_branch => {result}) in "
                    f"let {fallback} : (Delayed {self.typ(result_type)}) := Delayed.delayed {continuation} in {branch})"
                )
            return result
        raise ValueError(e)

    def pattern_test(self, pat, scrutinee, typ, yes, no, result_type):
        if pat[0] in ("wild", "unit"):
            return yes
        if pat[0] == "var":
            return f"(let {identifier(pat[1])} := {scrutinee} in {yes})"
        if pat[0] == "tuple":
            names = [self.fresh() for _ in pat[1:]]
            for p, n, t in reversed(list(zip(pat[1:], names, typ[1:], strict=True))):
                yes = self.pattern_test(p, n, t, yes, no, result_type)
            _, ctor = self.product_constructor(typ)
            return f"(match {scrutinee} with | {ctor} {' '.join(names)} => {yes})"
        assert pat[0] == "ctor"
        branches = []
        for ctor, (payload, owner) in self.ctors.items():
            if isinstance(owner, tuple) and isinstance(typ, tuple) and owner[:2] == typ[:2]:
                payload = substitute_type(payload, dict(zip(owner[2:], typ[2:], strict=True)))
                owner = typ
            if owner != typ:
                continue
            name = self.fresh()
            pattern = "C_" + ctor + (" " + name if payload != "unit" else "")
            body = self.pattern_test(pat[2], name, payload, yes, no, result_type) if ctor == pat[1] else no
            # Aeon's recursors evaluate nullary branch arguments eagerly.
            # Delay every branch so an unused fallthrough/error (or recursive
            # reference call) is never evaluated before selecting the branch.
            branches.append(
                f"| {pattern} => (let branch : (ignored:Bool) -> {self.typ(result_type)} := (fun delayed_branch => {body}) in Delayed.delayed branch)"
            )
        return f"(forceBranch (match {scrutinee} with {' '.join(branches)}))"

    def destructure(self, temporary, nested, typ, rhs):
        pattern, extra = self.pattern(nested, typ)
        for temp, pat, t in reversed(extra):
            rhs = self.destructure(temp, pat, t, rhs)
        return f"(match {temporary} with | {pattern} => {rhs})"

    def declarations(self, decls):
        code = []
        for tag, name, payload in decls:
            if tag == "type":
                code.append(f"inductive T_{name}")
                for ctor, typ in payload:
                    self.ctors[ctor] = (typ, name)
                    args = "" if typ == "unit" else f" (payload:{self.typ(typ)})"
                    code.append(f"| C_{ctor}{args} : T_{name}")
            else:
                typ = self.infer(payload, self.env)
                self.env[name] = typ
                code.append(f"def {identifier(name)} : {self.typ(typ)} := {self.expr(payload)};\n")
        return "\n".join(code) + "\n"

    def products(self):
        lines = [
            "inductive Delayed a",
            "| delayed (run:(ignored:Bool) -> a) : (Delayed a)",
            "def forceBranch (thunk:(Delayed a)) : a := match thunk with | delayed run => let call : (ignored:Bool) -> a := run in call true;",
        ]
        if self.monomorphic_products:
            done = set()
            while len(done) < len(self.product_types):
                typ = next(t for t in self.product_types if t not in done)
                done.add(typ)
                name, ctor = self.product_constructor(typ)
                fields = [self.typ(t) for t in typ[1:]]
                lines.extend(
                    [
                        f"inductive {name}",
                        f"| {ctor} " + " ".join(f"(x{i}:{t})" for i, t in enumerate(fields)) + f" : {name}",
                    ]
                )
                for i, t in enumerate(fields):
                    lines.append(
                        f"def project{name}_{i} (p:{name}) : {t} := match p with | {ctor} "
                        + " ".join(f"x{k}" for k in range(len(fields)))
                        + f" => x{i};"
                    )
            return "\n".join(lines) + "\n"
        for n in sorted(self.product_arities):
            types = [f"a{i}" for i in range(n)]
            result = f"(Product{n} {' '.join(types)})"
            lines += [
                f"inductive Product{n} {' '.join(types)}",
                f"| product{n} {' '.join(f'(x{i}:{t})' for i, t in enumerate(types))} : {result}",
            ]
            for i, t in enumerate(types):
                lines.append(
                    f"def projectProduct{n}_{i} (p:{result}) : {t} := match p with | product{n} {' '.join(f'x{k}' for k in range(n))} => x{i};"
                )
        return "\n".join(lines) + "\n"


def substitute_type(typ, substitution):
    if isinstance(typ, str):
        return substitution.get(typ, typ)
    return tuple(substitute_type(x, substitution) for x in typ)


def fix_type(expr):
    # nat_max in Burst/Trio annotates a curried two-argument lambda as
    # (nat * nat) -> nat. Preserve the body and repair that annotation.
    typ = expr[2]
    body = expr[3]
    if isinstance(typ, tuple) and typ[0] == "arrow" and isinstance(typ[1], tuple) and typ[1][0] == "prod":
        args = []
        while body[0] == "lam":
            args.append(body[2])
            body = body[3]
        if tuple(args) == typ[1][1:]:
            result = typ[2]
            for arg in reversed(args):
                result = ("arrow", arg, result)
            return result
    return typ


def translate(source):
    before, typ, after, (kind, spec) = Parser(source).problem()
    emitter = Emitter()
    prelude = emitter.declarations(before)
    # Keep specification-only helpers after the hole, outside its ingredients.
    spec_helpers = emitter.declarations(after)
    args, result = [], typ
    while isinstance(result, tuple) and result[0] == "arrow":
        args.append(result[1])
        result = result[2]
    binders = " ".join(f"(arg{i}:{emitter.typ(t)})" for i, t in enumerate(args))
    calls = " ".join(f"arg{i}" for i in range(len(args)))
    emitter.env.update({f"arg{i}": t for i, t in enumerate(args)})
    target = f"def target {binders} : {emitter.typ(result)} := ?hole;\n"
    if kind == "examples":
        assertions = []
        for inputs, output in spec:
            assert len(inputs) == len(args)
            assertions.append(f"@example(target {' '.join(emitter.expr(x) for x in inputs)} = {emitter.expr(output)})")
        code = prelude + "\n" + "\n".join(assertions) + "\n" + target
    else:
        if kind == "logical" and isinstance(args[0], tuple) and args[0][0] == "arrow":
            choices = [name for tag, name, _ in before + after if tag == "let" and emitter.env[name] == args[0]]
            assert choices, "A function-valued specification needs a concrete helper corpus"
            code = prelude + "\n" + target + spec_helpers
            for choice in choices:
                emitter.function_choice = choice
                rendered = emitter.expr(spec)
                spec_type = emitter.infer(spec, emitter.env)
                spec_name = "spec_for_" + identifier(choice)
                code += f"\ndef {spec_name} : {emitter.typ(spec_type)} := {rendered};\n"
                inputs = [("var", choice), *(("var", f"arg{i}") for i in range(1, len(args)))]
                packed = emitter.expr(("tuple", *inputs))
                actual = " ".join([identifier(choice), *(f"arg{i}" for i in range(1, len(args)))])
                check = f"({spec_name} {packed} (target {actual}))"
                code += (
                    f"@property(100)\ndef property_{identifier(choice)} "
                    + " ".join(f"(arg{i}:{emitter.typ(t)})" for i, t in enumerate(args) if i > 0)
                    + f" : Bool := match {check} with | C_True => true | C_False => false;\n"
                )
            return emitter.products() + code, "named-function-properties", len(choices)
        rendered = emitter.expr(spec)
        spec_type = emitter.infer(spec, emitter.env)
        spec_helpers += f"\ndef original_specification : {emitter.typ(spec_type)} := {rendered};\n"
        rendered = "original_specification"
        if kind == "reference":
            reference_args = calls
            if len(args) > 1 and spec_type[1] == ("prod", *args):
                reference_args = emitter.expr(("tuple", *(("var", f"arg{i}") for i in range(len(args)))))
            check = f"(target {calls}) = ({rendered} {reference_args})"
        else:
            inputs = [("var", f"arg{i}") for i in range(len(args))]
            packed = inputs[0] if len(inputs) == 1 else ("tuple", *inputs)
            check = f"({rendered} {emitter.expr(packed)} (target {calls}))"
            final_type = spec_type
            while isinstance(final_type, tuple) and final_type[0] == "arrow":
                final_type = final_type[2]
            if final_type == "bool":
                check = f"(match {check} with | C_True => true | C_False => false)"
        code = (
            prelude
            + "\n"
            + target
            + spec_helpers
            + f"\n@property(100)\ndef specification {binders} : Bool := {check};\n"
        )
    return emitter.products() + code, kind, len(spec) if kind == "examples" else 1


def ml_suites(corpus, selected=None):
    suites = [
        ("burst", "burst/burst/benchmarks", ["io", "ref", "logical"]),
        ("trio", "trio/test", ["io", "ref"]),
        ("guide", "guide/test", ["auto_gen"]),
        ("trio-jfp", "trio-jfp/benchmarks", ["io", "ref"]),
    ]
    for suite, root, variants in suites:
        if selected is not None and suite not in selected:
            continue
        for variant in variants:
            for path in sorted((corpus.source_root / root / variant).glob("*.mls")):
                code, kind, count = translate(read_source(path))
                corpus.add(
                    f"{suite}/{variant}",
                    path.stem,
                    path,
                    code,
                    specification=kind,
                    examples=count if kind == "examples" else 0,
                    properties=0 if kind == "examples" else count,
                )
