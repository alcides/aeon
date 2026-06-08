"""AeonDoc generator - extracts documentation from Aeon source files and generates HTML."""

from __future__ import annotations

import html
import re
from dataclasses import dataclass, field
from pathlib import Path

from aeon.sugar.program import (
    Program,
    Decorator,
    STerm,
    SLiteral,
    SVar,
    SQualifiedVar,
    SAnnotation,
    SHole,
    SApplication,
    SAbstraction,
    SLet,
    SRec,
    SIf,
)
from aeon.sugar.parser import parse_main_program
from aeon.sugar.bind import bind_program
from aeon.sugar.stypes import (
    SType,
    STypeVar,
    SRefinedType,
    SAbstractionType,
    STypePolymorphism,
    SRefinementPolymorphism,
    STypeConstructor,
)
from aeon.core.multiplicity import MOmega
from aeon.utils.name import Name


@dataclass
class DocComment:
    """Represents a documentation comment extracted from source."""

    text: str
    line_number: int


@dataclass
class TypeDoc:
    """Documentation for a type declaration."""

    name: str
    args: list[str]
    rforalls: list[tuple[str, str]]
    comment: str | None
    line_number: int
    is_inductive: bool = False
    constructors: list[ConstructorDoc] | None = None
    measures: list[ConstructorDoc] | None = None


@dataclass
class ConstructorDoc:
    """Documentation for a constructor or measure."""

    name: str
    type_sig: str
    comment: str | None
    line_number: int


@dataclass
class FunctionDoc:
    """Documentation for a function definition."""

    name: str
    type_sig: str
    args: list[tuple[str, str]]
    decorators: list[str]
    comment: str | None
    line_number: int
    foralls: list[tuple[str, str]]
    rforalls: list[tuple[str, str]]
    arg_docs: dict[str, str] = field(default_factory=dict)
    return_doc: str | None = None
    is_uninterpreted: bool = False
    # Surface renderings of each ``@example(...)`` assertion attached to this
    # function. Shown as worked, machine-checked examples in the docs.
    examples: list[str] = field(default_factory=list)
    # Head name of this function's final return type (after peeling
    # arrows / refinements / quantifiers). ``None`` if the head isn't a named
    # type constructor — e.g. the function returns a polymorphic ``a``.
    returns_type_head: str | None = None


@dataclass
class ModuleDoc:
    """Complete documentation for a module."""

    filename: str
    imports: list[str]
    types: list[TypeDoc]
    functions: list[FunctionDoc]
    header_comment: str | None = None


def extract_comments(source: str) -> dict[int, str]:
    """
    Extract all comments from source code.
    Returns a mapping from line number to comment text.
    """
    comments = {}
    lines = source.split("\n")

    for i, line in enumerate(lines, start=1):
        stripped = line.strip()
        if stripped.startswith("#"):
            comment_text = stripped[1:].strip()
            comments[i] = comment_text

    return comments


def find_preceding_comment(comments: dict[int, str], target_line: int) -> str | None:
    """
    Find the comment immediately preceding a given line.
    Returns the concatenated comment text or None.
    """
    comment_lines: list[str] = []
    check_line = target_line - 1

    while check_line in comments:
        comment_lines.insert(0, comments[check_line])
        check_line -= 1

    if comment_lines:
        return "\n".join(comment_lines)
    return None


def find_header_comment(source: str, first_decl_line: int | None) -> str | None:
    """Extract module-level header comment at the beginning of the file."""
    lines = source.split("\n")
    comment_lines: list[str] = []

    for i, line in enumerate(lines, start=1):
        if first_decl_line and i >= first_decl_line:
            break
        stripped = line.strip()
        if stripped.startswith("#"):
            comment_lines.append(stripped[1:].strip())
        elif stripped and not stripped.startswith("import") and not stripped.startswith("open"):
            break

    if comment_lines:
        return "\n".join(comment_lines)
    return None


_ARG_DOC_RE = re.compile(r"^([A-Za-z_]\w*)\s*:\s*(.+)$")


def split_arg_docs(comment: str | None) -> tuple[str | None, dict[str, str], str | None]:
    """Split a function comment into (header description, per-arg docs, return doc).

    Lines matching ``argname: description`` become per-arg docs. The special name
    ``returns`` (or ``return``) is captured separately. Lines preceding the first
    such line form the header description. Plain continuation lines are folded
    into the preceding arg doc.
    """
    if not comment:
        return None, {}, None

    header_lines: list[str] = []
    arg_docs: dict[str, str] = {}
    return_doc: str | None = None
    current: str | None = None
    seen_arg_line = False

    for raw in comment.split("\n"):
        m = _ARG_DOC_RE.match(raw.strip())
        if m:
            key = m.group(1)
            value = m.group(2).strip()
            if key in ("returns", "return"):
                return_doc = value
                current = "__return__"
            else:
                arg_docs[key] = value
                current = key
            seen_arg_line = True
        elif current and raw.strip() and seen_arg_line:
            if current == "__return__" and return_doc is not None:
                return_doc += " " + raw.strip()
            elif current in arg_docs:
                arg_docs[current] += " " + raw.strip()
        else:
            header_lines.append(raw)
            current = None

    header = "\n".join(header_lines).strip() or None
    return header, arg_docs, return_doc


def format_name(name: Name) -> str:
    """Render a Name for docs using its surface spelling — no alpha-renaming superscript."""
    return name.name


# Operator precedence ladder used to pretty-print refinements in infix form.
# Higher number = binds tighter. Function application sits above any binary op.
_PREC_TOP = 0
_PREC_OR = 1
_PREC_AND = 2
_PREC_EQ = 3
_PREC_REL = 4
_PREC_ADD = 5
_PREC_MUL = 6
_PREC_APP = 7
_PREC_ATOM = 8

_BINARY_OPS: dict[str, int] = {
    "||": _PREC_OR,
    "&&": _PREC_AND,
    "==": _PREC_EQ,
    "!=": _PREC_EQ,
    "<": _PREC_REL,
    "<=": _PREC_REL,
    ">": _PREC_REL,
    ">=": _PREC_REL,
    "+": _PREC_ADD,
    "-": _PREC_ADD,
    "*": _PREC_MUL,
    "/": _PREC_MUL,
    "%": _PREC_MUL,
    "++": _PREC_ADD,
}


def _flatten_app(term: STerm) -> tuple[STerm, list[STerm]]:
    """Flatten left-leaning ``SApplication`` chain into ``(head, [args left-to-right])``."""
    args: list[STerm] = []
    cur: STerm = term
    while isinstance(cur, SApplication):
        args.insert(0, cur.arg)
        cur = cur.fun
    return cur, args


def _as_binary_op(term: STerm) -> tuple[str, STerm, STerm] | None:
    """If ``term`` is ``((op lhs) rhs)`` with ``op`` a known infix operator, return it."""
    if isinstance(term, SApplication) and isinstance(term.fun, SApplication) and isinstance(term.fun.fun, SVar):
        op = term.fun.fun.name.name
        if op in _BINARY_OPS:
            return op, term.fun.arg, term.arg
    return None


def format_term(term: STerm, min_prec: int = _PREC_TOP) -> str:
    """Render an STerm for docs using surface spellings and infix operators.

    ``min_prec`` is the precedence the surrounding context expects; if the term's
    own precedence is lower it gets parenthesized.
    """
    binop = _as_binary_op(term)
    if binop is not None:
        op, lhs, rhs = binop
        p = _BINARY_OPS[op]
        # Left-associative: left side accepts equal precedence, right side requires strictly higher.
        result = f"{format_term(lhs, p)} {op} {format_term(rhs, p + 1)}"
        return f"({result})" if p < min_prec else result

    if isinstance(term, SApplication):
        head, args = _flatten_app(term)
        head_s = format_term(head, _PREC_APP)
        args_s = " ".join(format_term(a, _PREC_ATOM) for a in args)
        result = f"{head_s} {args_s}"
        return f"({result})" if _PREC_APP < min_prec else result

    match term:
        case SLiteral(value, ty, _):
            if isinstance(ty, STypeConstructor) and ty.name.name == "String":
                return f'"{value}"'
            return f"{value}"
        case SVar(name, _):
            return format_name(name)
        case SQualifiedVar(qualifier, name, _):
            return f"{qualifier}.{format_name(name)}"
        case SAnnotation(expr, ty, _):
            return f"({format_term(expr)} : {format_type(ty)})"
        case SHole(name, _):
            return f"?{format_name(name)}"
        case SAbstraction(var_name, body, _):
            inner = f"fun {format_name(var_name)} => {format_term(body)}"
            return f"({inner})" if min_prec > _PREC_TOP else inner
        case SLet(var_name, var_value, body, _, _):
            inner = f"let {format_name(var_name)} = {format_term(var_value)} in {format_term(body)}"
            return f"({inner})" if min_prec > _PREC_TOP else inner
        case SRec():
            inner = (
                f"let {format_name(term.var_name)} : {format_type(term.var_type)} = "
                f"{format_term(term.var_value)} in {format_term(term.body)}"
            )
            return f"({inner})" if min_prec > _PREC_TOP else inner
        case SIf(cond, then, otherwise, _):
            inner = f"if {format_term(cond)} then {format_term(then)} else {format_term(otherwise)}"
            return f"({inner})" if min_prec > _PREC_TOP else inner
        case _:
            return str(term)


def format_type(stype: SType) -> str:
    """Format a type for display.

    Like ``str(stype)`` but strips the leading ``'`` that ``STypeVar.__str__``
    prepends and renders names by their surface spelling (no alpha-renaming
    superscript), so a reference to a type just looks like ``Image``, not ``'Image⁵``.
    """
    match stype:
        case STypeVar(name):
            return format_name(name)
        case SRefinedType(name, ty, refinement):
            return f"{{{format_name(name)} : {format_type(ty)} | {format_term(refinement)}}}"
        case SAbstractionType(var_name, var_type, body):
            prefix = "" if stype.multiplicity is MOmega else f"{stype.multiplicity} "
            return f"({prefix}{format_name(var_name)} : {format_type(var_type)}) -> {format_type(body)}"
        case STypePolymorphism(name, kind, body):
            return f"∀{format_name(name)}:{kind}. {format_type(body)}"
        case SRefinementPolymorphism(name, sort, body):
            return f"∀<{format_name(name)}:{format_type(sort)} -> Bool>. {format_type(body)}"
        case STypeConstructor(name, args):
            if not args:
                return format_name(name)
            return f"{format_name(name)} {' '.join(format_type(a) for a in args)}"
        case _:
            return str(stype)


def format_decorator(dec: Decorator) -> str:
    """Format a decorator for display."""
    return repr(dec)


def return_type_head(stype: SType) -> str | None:
    """Peel arrows / refinements / quantifiers off ``stype`` and return the head
    type-constructor name, or ``None`` if the head is not a named constructor.

    Used to identify constructor-like ``mk*`` functions: a function that
    ultimately returns ``Image`` (possibly inside a refinement, after some
    parameters) has head name ``"Image"``.
    """
    cur = stype
    while True:
        if isinstance(cur, SAbstractionType):
            cur = cur.type
        elif isinstance(cur, SRefinedType):
            cur = cur.type
        elif isinstance(cur, STypePolymorphism):
            cur = cur.body
        elif isinstance(cur, SRefinementPolymorphism):
            cur = cur.body
        else:
            break
    if isinstance(cur, STypeVar):
        return cur.name.name
    if isinstance(cur, STypeConstructor):
        return cur.name.name
    return None


def extract_documentation(filename: str, source: str | None = None) -> ModuleDoc:
    """
    Extract documentation from an Aeon source file.

    Args:
        filename: Path to the .ae file
        source: Optional source code (if None, will read from filename)

    Returns:
        ModuleDoc containing all extracted documentation
    """
    if source is None:
        with open(filename, encoding="utf-8") as f:
            source = f.read()

    prog: Program = parse_main_program(source, filename=filename)
    prog = bind_program(prog, [])

    comments = extract_comments(source)

    first_decl_line = None
    all_decls = list(prog.type_decls) + list(prog.inductive_decls) + list(prog.definitions)
    if all_decls:
        first_decl_line = min(d.loc.start[0] if hasattr(d.loc, "start") else 1 for d in all_decls if hasattr(d, "loc"))

    header_comment = find_header_comment(source, first_decl_line)

    imports = []
    for imp in prog.imports:
        imports.append(str(imp))

    types = []
    for type_decl in prog.type_decls:
        line_num = type_decl.loc.start[0] if hasattr(type_decl.loc, "start") else 0
        comment = find_preceding_comment(comments, line_num)

        args_str = [format_name(arg) if isinstance(arg, Name) else str(arg) for arg in type_decl.args]
        rforalls_formatted = [(format_name(n), format_type(s)) for n, s in type_decl.rforalls]

        types.append(
            TypeDoc(
                name=format_name(type_decl.name),
                args=args_str,
                rforalls=rforalls_formatted,
                comment=comment,
                line_number=line_num,
                is_inductive=False,
            )
        )

    for inductive in prog.inductive_decls:
        line_num = inductive.loc.start[0] if hasattr(inductive.loc, "start") else 0
        comment = find_preceding_comment(comments, line_num)

        args_str = [format_name(arg) if isinstance(arg, Name) else str(arg) for arg in inductive.args]
        rforalls_formatted = [(format_name(n), format_type(s)) for n, s in inductive.rforalls]

        constructors = []
        for cons in inductive.constructors:
            cons_line = cons.loc.start[0] if hasattr(cons.loc, "start") else 0
            cons_comment = find_preceding_comment(comments, cons_line)
            constructors.append(
                ConstructorDoc(
                    name=format_name(cons.name),
                    type_sig=format_type(cons.type),
                    comment=cons_comment,
                    line_number=cons_line,
                )
            )

        measures = []
        for meas in inductive.measures:
            meas_line = meas.loc.start[0] if hasattr(meas.loc, "start") else 0
            meas_comment = find_preceding_comment(comments, meas_line)
            measures.append(
                ConstructorDoc(
                    name=format_name(meas.name),
                    type_sig=format_type(meas.type),
                    comment=meas_comment,
                    line_number=meas_line,
                )
            )

        types.append(
            TypeDoc(
                name=format_name(inductive.name),
                args=args_str,
                rforalls=rforalls_formatted,
                comment=comment,
                line_number=line_num,
                is_inductive=True,
                constructors=constructors if constructors else None,
                measures=measures if measures else None,
            )
        )

    functions = []
    for defn in prog.definitions:
        line_num = defn.loc.start[0] if hasattr(defn.loc, "start") else 0
        raw_comment = find_preceding_comment(comments, line_num)
        # Don't shadow the outer module-level ``header_comment``.
        func_header_comment, arg_docs, return_doc = split_arg_docs(raw_comment)

        args_formatted = [(format_name(n), format_type(t)) for n, t in defn.args]
        # ``@example(assertion)`` decorators are surfaced in their own block; the
        # remaining decorators are shown as chips.
        examples_formatted = [
            format_term(dec.macro_args[0]) for dec in defn.decorators if dec.name.name == "example" and dec.macro_args
        ]
        decorators_formatted = [format_decorator(dec) for dec in defn.decorators if dec.name.name != "example"]
        foralls_formatted = [(format_name(n), str(k)) for n, k in defn.foralls]
        rforalls_formatted = [(format_name(n), format_type(s)) for n, s in defn.rforalls]

        # An uninterpreted function is one declared as ``def f ... = uninterpreted``;
        # in the sugar AST this is the bare reference ``SVar(Name("uninterpreted", _))``.
        # (``native "..."`` bodies are ``SApplication`` and don't match.)
        is_uninterpreted = isinstance(defn.body, SVar) and defn.body.name.name == "uninterpreted"

        functions.append(
            FunctionDoc(
                name=format_name(defn.name),
                type_sig=format_type(defn.type),
                args=args_formatted,
                decorators=decorators_formatted,
                comment=func_header_comment,
                line_number=line_num,
                foralls=foralls_formatted,
                rforalls=rforalls_formatted,
                arg_docs=arg_docs,
                return_doc=return_doc,
                is_uninterpreted=is_uninterpreted,
                returns_type_head=return_type_head(defn.type),
                examples=examples_formatted,
            )
        )

    return ModuleDoc(
        filename=filename, imports=imports, types=types, functions=functions, header_comment=header_comment
    )


def generate_html(doc: ModuleDoc, output_path: str | None = None) -> str:
    """
    Generate self-contained HTML documentation from ModuleDoc.

    Args:
        doc: The module documentation
        output_path: Optional path to write the HTML file

    Returns:
        The generated HTML as a string
    """
    html_parts = []

    module_name = Path(doc.filename).stem

    html_parts.append(
        f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{html.escape(module_name)} - Aeon Documentation</title>
    <style>
        * {{
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }}
        body {{
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, 'Helvetica Neue', Arial, sans-serif;
            line-height: 1.6;
            color: #333;
            background: #f5f5f5;
            padding: 20px;
        }}
        .container {{
            max-width: 1200px;
            margin: 0 auto;
            background: white;
            padding: 40px;
            /* Bottom buffer so the last anchored item can scroll up to the top
               of the viewport when a TOC link is clicked. */
            padding-bottom: max(40px, 70vh);
            box-shadow: 0 2px 8px rgba(0,0,0,0.1);
            border-radius: 8px;
        }}
        html {{
            /* Anchor-scroll lands the target a little below the viewport's top
               edge, so the section header doesn't sit flush against it. */
            scroll-padding-top: 20px;
            scroll-behavior: smooth;
        }}
        :target {{
            /* Brief highlight when an anchor is jumped to, to signal "you landed here". */
            animation: anchor-flash 1.2s ease-out 1;
        }}
        @keyframes anchor-flash {{
            0% {{ background-color: #fef9c3; }}
            100% {{ background-color: transparent; }}
        }}
        h1 {{
            color: #2c3e50;
            border-bottom: 3px solid #3498db;
            padding-bottom: 10px;
            margin-bottom: 30px;
            font-size: 2.5em;
        }}
        h2 {{
            color: #34495e;
            margin-top: 40px;
            margin-bottom: 20px;
            font-size: 1.8em;
            border-bottom: 2px solid #ecf0f1;
            padding-bottom: 8px;
        }}
        h3 {{
            color: #2980b9;
            margin-top: 25px;
            margin-bottom: 15px;
            font-size: 1.3em;
        }}
        .header-comment {{
            background: #ecf0f1;
            padding: 20px;
            border-left: 4px solid #3498db;
            margin-bottom: 30px;
            border-radius: 4px;
            white-space: pre-wrap;
            font-style: italic;
        }}
        .imports {{
            background: #f8f9fa;
            padding: 15px;
            border-radius: 4px;
            margin-bottom: 30px;
        }}
        .imports code {{
            display: block;
            color: #7f8c8d;
            padding: 2px 0;
        }}
        .item {{
            margin-bottom: 35px;
            padding: 20px;
            background: #fafafa;
            border-radius: 6px;
            border: 1px solid #e1e4e8;
        }}
        .item.uninterpreted {{
            background: #fffbeb;
            border-color: #fde68a;
        }}
        .badge {{
            display: inline-block;
            padding: 2px 10px;
            border-radius: 12px;
            font-size: 0.78em;
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
            font-weight: 600;
            letter-spacing: 0.02em;
            text-transform: uppercase;
            cursor: help;
        }}
        .badge-uninterpreted {{
            background: #fef3c7;
            color: #92400e;
            border: 1px solid #fcd34d;
        }}
        .badge-ctor {{
            background: #ecfdf5;
            color: #047857;
            border: 1px solid #6ee7b7;
        }}
        .section-note {{
            color: #555;
            font-size: 0.95em;
            margin: 0 0 18px 0;
        }}
        .ctor-group {{
            margin: 18px 0 28px 0;
        }}
        .ctor-group-header {{
            margin: 14px 0 10px 0;
        }}
        .ctor-type-link {{
            color: #2980b9;
            text-decoration: none;
        }}
        .ctor-type-link:hover {{
            text-decoration: underline;
        }}
        .ctor-item {{
            margin-left: 18px;
            border-left: 3px solid #6ee7b7;
        }}
        .toc-note {{
            color: #7f8c8d;
            font-size: 0.85em;
            font-style: italic;
        }}
        .subhead {{
            /* Non-heading sub-label inside an item (e.g. "Measures" inside an
               inductive type). Looks like a small heading but is not a heading
               element, so the page heading hierarchy stays aligned with the TOC. */
            margin: 14px 0 8px 0;
            font-weight: 600;
            color: #34495e;
            font-size: 0.95em;
            text-transform: uppercase;
            letter-spacing: 0.04em;
        }}
        .toc .toc-uninterpreted::after {{
            content: "uninterpreted";
            display: inline-block;
            margin-left: 6px;
            padding: 0 6px;
            font-size: 0.7em;
            font-weight: 600;
            text-transform: uppercase;
            background: #fef3c7;
            color: #92400e;
            border: 1px solid #fcd34d;
            border-radius: 8px;
            vertical-align: 1px;
        }}
        .item-header {{
            display: flex;
            align-items: baseline;
            gap: 10px;
            margin-bottom: 10px;
        }}
        .item-name {{
            font-size: 1.4em;
            font-weight: bold;
            color: #2c3e50;
            font-family: 'Courier New', monospace;
        }}
        .item-type {{
            color: #7f8c8d;
            font-size: 0.9em;
        }}
        .signature {{
            background: #f1f3f5;
            padding: 12px;
            border-left: 3px solid #2980b9;
            margin: 10px 0;
            font-family: 'Courier New', monospace;
            overflow: visible;
            border-radius: 4px;
        }}
        .sig-arg, .sig-return {{
            display: inline-block;
            padding: 1px 6px;
            border-radius: 4px;
            cursor: help;
            position: relative;
            transition: filter 0.15s ease, box-shadow 0.15s ease;
        }}
        .sig-arg:hover, .sig-return:hover {{
            filter: brightness(0.94);
            box-shadow: 0 0 0 1px rgba(0,0,0,0.08);
        }}
        .sig-arg-0 {{ background-color: #fef3c7; }}
        .sig-arg-1 {{ background-color: #dbeafe; }}
        .sig-arg-2 {{ background-color: #dcfce7; }}
        .sig-arg-3 {{ background-color: #fce7f3; }}
        .sig-arg-4 {{ background-color: #e0e7ff; }}
        .sig-arg-5 {{ background-color: #fed7aa; }}
        .sig-arg-6 {{ background-color: #f3e8ff; }}
        .sig-arg-7 {{ background-color: #ccfbf1; }}
        .sig-return {{ background-color: #f1f5f9; border: 1px dashed #94a3b8; }}
        .sig-arg[data-tooltip]:hover::after,
        .sig-return[data-tooltip]:hover::after {{
            content: attr(data-tooltip);
            position: absolute;
            bottom: calc(100% + 8px);
            left: 0;
            background: #1f2937;
            color: #f9fafb;
            padding: 8px 12px;
            border-radius: 6px;
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
            font-size: 0.85em;
            line-height: 1.4;
            white-space: pre-wrap;
            width: max-content;
            max-width: 420px;
            z-index: 20;
            box-shadow: 0 4px 12px rgba(0,0,0,0.18);
            pointer-events: none;
        }}
        .sig-arg[data-tooltip]:hover::before,
        .sig-return[data-tooltip]:hover::before {{
            content: "";
            position: absolute;
            bottom: calc(100% + 2px);
            left: 14px;
            border: 6px solid transparent;
            border-top-color: #1f2937;
            z-index: 20;
            pointer-events: none;
        }}
        .comment {{
            color: #555;
            margin: 12px 0;
            padding: 12px;
            background: white;
            border-left: 3px solid #27ae60;
            border-radius: 4px;
            white-space: pre-wrap;
        }}
        .decorators {{
            margin: 8px 0;
            display: flex;
            flex-wrap: wrap;
            gap: 6px;
        }}
        .decorator {{
            background: #9b59b6;
            color: white;
            padding: 4px 10px;
            border-radius: 12px;
            font-size: 0.85em;
            font-family: 'Courier New', monospace;
        }}
        .examples {{
            margin: 12px 0;
        }}
        .examples-title {{
            font-weight: 600;
            color: #34495e;
            font-size: 0.85em;
            text-transform: uppercase;
            letter-spacing: 0.04em;
            margin-bottom: 6px;
        }}
        .example {{
            font-family: 'Courier New', monospace;
            background: #eef6ff;
            border-left: 3px solid #2980b9;
            padding: 6px 10px;
            margin: 4px 0;
            border-radius: 4px;
            white-space: pre-wrap;
        }}
        .constructor {{
            margin-left: 20px;
            padding: 10px;
            background: white;
            border-radius: 4px;
            margin-bottom: 8px;
        }}
        .constructor-name {{
            font-weight: bold;
            color: #16a085;
            font-family: 'Courier New', monospace;
        }}
        .toc {{
            background: #f8f9fa;
            padding: 20px;
            border-radius: 6px;
            margin-bottom: 30px;
        }}
        .toc-title, .imports-title {{
            /* Non-heading labels — kept out of the document outline so the
               page outline matches the TOC contents exactly. */
            margin: 0 0 10px 0;
            font-weight: bold;
            color: #2c3e50;
            font-size: 1.3em;
        }}
        .imports-title {{
            color: #2980b9;
        }}
        .toc ul {{
            list-style: none;
            padding-left: 20px;
        }}
        .toc li {{
            margin: 6px 0;
        }}
        .toc a {{
            color: #2980b9;
            text-decoration: none;
        }}
        .toc a:hover {{
            text-decoration: underline;
        }}
        code {{
            font-family: 'Courier New', monospace;
            background: #f1f3f5;
            padding: 2px 6px;
            border-radius: 3px;
            font-size: 0.95em;
        }}
        .type-link {{
            color: #2980b9;
            cursor: pointer;
            text-decoration: none;
        }}
        .type-link:hover {{
            text-decoration: underline;
        }}
        .args-list {{
            margin: 10px 0;
        }}
        .arg {{
            padding: 4px 0;
            font-family: 'Courier New', monospace;
        }}
    </style>
</head>
<body>
    <div class="container">
        <h1>{html.escape(module_name)}</h1>
"""
    )

    if doc.header_comment:
        html_parts.append(f'        <div class="header-comment">{html.escape(doc.header_comment)}</div>\n')

    if doc.imports:
        html_parts.append('        <div class="imports">\n')
        # Meta-section label — not in the TOC, so not a heading element.
        html_parts.append('            <div class="imports-title">Imports</div>\n')
        for imp in doc.imports:
            html_parts.append(f"            <code>{html.escape(imp)}</code>\n")
        html_parts.append("        </div>\n")

    # Partition functions into regular vs uninterpreted.
    regular_functions = [f for f in doc.functions if not f.is_uninterpreted]
    uninterpreted_functions = [f for f in doc.functions if f.is_uninterpreted]

    # Build the constructor index: for each type in this module, collect its
    # constructors. Inductive types use their declared constructors; opaque
    # types use the convention "any local function whose name starts with `mk`
    # and which returns a value of that type is a constructor".
    constructors_by_type: list[tuple[TypeDoc, list[dict]]] = []
    for t in doc.types:
        entries: list[dict] = []
        if t.is_inductive and t.constructors:
            for c in t.constructors:
                entries.append(
                    {
                        "kind": "inductive",
                        "name": c.name,
                        "type_sig": c.type_sig,
                        "comment": c.comment,
                        "line_number": c.line_number,
                        "func": None,
                    }
                )
        elif not t.is_inductive:
            for f in doc.functions:
                if f.name.startswith("mk") and f.returns_type_head == t.name:
                    entries.append(
                        {
                            "kind": "mk",
                            "name": f.name,
                            "type_sig": f.type_sig,
                            "comment": f.comment,
                            "line_number": f.line_number,
                            "func": f,
                        }
                    )
        if entries:
            constructors_by_type.append((t, entries))

    html_parts.append('        <div class="toc">\n')
    # Meta-section label — not in the TOC itself, so not a heading element.
    html_parts.append('            <div class="toc-title">Table of Contents</div>\n')
    html_parts.append("            <ul>\n")
    if doc.types:
        html_parts.append('                <li><a href="#types">Types</a>\n')
        html_parts.append("                    <ul>\n")
        for t in doc.types:
            anchor = f"type-{html.escape(t.name)}-L{t.line_number}"
            html_parts.append(f'                        <li><a href="#{anchor}">{html.escape(t.name)}</a></li>\n')
        html_parts.append("                    </ul>\n")
        html_parts.append("                </li>\n")
    if constructors_by_type:
        html_parts.append('                <li><a href="#constructors">Constructors</a>\n')
        html_parts.append("                    <ul>\n")
        for t, entries in constructors_by_type:
            t_anchor = f"ctor-type-{html.escape(t.name)}-L{t.line_number}"
            kind_label = "inductive" if t.is_inductive else "opaque, mk*"
            html_parts.append(
                f'                        <li><a href="#{t_anchor}">{html.escape(t.name)}</a>'
                f' <span class="toc-note">({kind_label})</span>\n'
            )
            html_parts.append("                            <ul>\n")
            for e in entries:
                e_anchor = f"ctor-{html.escape(t.name)}-{html.escape(e['name'])}-L{e['line_number']}"
                html_parts.append(
                    f'                                <li><a href="#{e_anchor}">{html.escape(e["name"])}</a></li>\n'
                )
            html_parts.append("                            </ul>\n")
            html_parts.append("                        </li>\n")
        html_parts.append("                    </ul>\n")
        html_parts.append("                </li>\n")
    if regular_functions:
        html_parts.append('                <li><a href="#functions">Functions</a>\n')
        html_parts.append("                    <ul>\n")
        for f in regular_functions:
            anchor = f"func-{html.escape(f.name)}-L{f.line_number}"
            html_parts.append(f'                        <li><a href="#{anchor}">{html.escape(f.name)}</a></li>\n')
        html_parts.append("                    </ul>\n")
        html_parts.append("                </li>\n")
    if uninterpreted_functions:
        html_parts.append('                <li><a href="#uninterpreted">Uninterpreted</a>\n')
        html_parts.append("                    <ul>\n")
        for f in uninterpreted_functions:
            anchor = f"func-{html.escape(f.name)}-L{f.line_number}"
            html_parts.append(
                f'                        <li><a href="#{anchor}" class="toc-uninterpreted">'
                f"{html.escape(f.name)}</a></li>\n"
            )
        html_parts.append("                    </ul>\n")
        html_parts.append("                </li>\n")
    html_parts.append("            </ul>\n")
    html_parts.append("        </div>\n")

    if doc.types:
        html_parts.append('        <h2 id="types">Types</h2>\n')
        for type_doc in doc.types:
            anchor = f"type-{html.escape(type_doc.name)}-L{type_doc.line_number}"
            html_parts.append(f'        <div class="item" id="{anchor}">\n')
            html_parts.append('            <div class="item-header">\n')

            type_kind = "inductive" if type_doc.is_inductive else "type"
            # h3 — sits directly under <h2 id="types"> and is the page heading
            # that the TOC entry "Types › {name}" targets.
            html_parts.append(f'                <h3 class="item-name">{html.escape(type_doc.name)}</h3>\n')
            html_parts.append(f'                <span class="item-type">({type_kind})</span>\n')
            html_parts.append("            </div>\n")

            if type_doc.comment:
                html_parts.append(f'            <div class="comment">{html.escape(type_doc.comment)}</div>\n')

            sig_parts = [type_kind, type_doc.name]
            if type_doc.args:
                sig_parts.extend(type_doc.args)
            if type_doc.rforalls:
                for name, sort in type_doc.rforalls:
                    sig_parts.append(f"forall <{name}:{sort} -> Bool>")

            html_parts.append(f'            <div class="signature">{html.escape(" ".join(sig_parts))}</div>\n')

            # Inductive constructors are listed in the dedicated Constructors section
            # below — no need to duplicate them here. Measures (which don't appear in
            # the TOC) get a non-heading sub-label so the page-heading hierarchy
            # stays in lock-step with the TOC.
            if type_doc.is_inductive and type_doc.measures:
                html_parts.append('            <div class="subhead">Measures</div>\n')
                for meas in type_doc.measures:
                    html_parts.append('            <div class="constructor">\n')
                    html_parts.append(
                        f'                <span class="constructor-name">{html.escape(meas.name)}</span>'
                        f" : <code>{html.escape(meas.type_sig)}</code>\n"
                    )
                    if meas.comment:
                        html_parts.append(f'                <div class="comment">{html.escape(meas.comment)}</div>\n')
                    html_parts.append("            </div>\n")

            html_parts.append("        </div>\n")

    def render_function_item(func: FunctionDoc, anchor: str, extra_classes: str = "", heading_tag: str = "h3") -> None:
        """Append a full function-item card with colored args + tooltips to html_parts.

        ``heading_tag`` selects the heading element used for the item's name. Items
        that sit directly under an h2 section use ``h3``; items nested under a
        per-type h3 group (constructors inside the Constructors section) use ``h4``.
        """
        item_classes = "item"
        if func.is_uninterpreted:
            item_classes += " uninterpreted"
        if extra_classes:
            item_classes += " " + extra_classes
        html_parts.append(f'        <div class="{item_classes}" id="{anchor}">\n')
        html_parts.append('            <div class="item-header">\n')
        html_parts.append(
            f'                <{heading_tag} class="item-name">{html.escape(func.name)}</{heading_tag}>\n'
        )
        if func.is_uninterpreted:
            html_parts.append(
                '                <span class="badge badge-uninterpreted"'
                ' title="Declared as `def ... = uninterpreted`: no body. The verifier treats it as'
                ' an uninterpreted function — only its signature is known.">uninterpreted</span>\n'
            )
        html_parts.append("            </div>\n")

        if func.decorators:
            html_parts.append('            <div class="decorators">\n')
            for dec in func.decorators:
                html_parts.append(f'                <span class="decorator">{html.escape(dec)}</span>\n')
            html_parts.append("            </div>\n")

        if func.comment:
            html_parts.append(f'            <div class="comment">{html.escape(func.comment)}</div>\n')

        if func.examples:
            html_parts.append('            <div class="examples">\n')
            html_parts.append('                <div class="examples-title">Examples</div>\n')
            for ex in func.examples:
                html_parts.append(f'                <div class="example">{html.escape(ex)}</div>\n')
            html_parts.append("            </div>\n")

        sig_html_parts: list[str] = [html.escape(f"def {func.name}")]

        if func.foralls:
            for fname, fkind in func.foralls:
                sig_html_parts.append(html.escape(f"∀{fname}:{fkind}"))

        if func.rforalls:
            for rname, rsort in func.rforalls:
                sig_html_parts.append(html.escape(f"∀<{rname}:{rsort} -> Bool>"))

        for idx, (arg_name, arg_type) in enumerate(func.args):
            doc_text = func.arg_docs.get(arg_name)
            tooltip = f"{arg_name} : {arg_type}"
            if doc_text:
                tooltip += f"\n\n{doc_text}"
            color_class = f"sig-arg-{idx % 8}"
            sig_html_parts.append(
                f'<span class="sig-arg {color_class}" data-tooltip="{html.escape(tooltip, quote=True)}">'
                f"({html.escape(arg_name)}: {html.escape(arg_type)})"
                f"</span>"
            )

        return_html = html.escape(func.type_sig)
        if func.return_doc:
            return_tooltip = f"returns: {func.return_doc}"
            return_html = (
                f'<span class="sig-return" data-tooltip="{html.escape(return_tooltip, quote=True)}">'
                f"{return_html}</span>"
            )
        sig_html_parts.append(":")
        sig_html_parts.append(return_html)

        html_parts.append(f'            <div class="signature">{" ".join(sig_html_parts)}</div>\n')
        html_parts.append("        </div>\n")

    if constructors_by_type:
        html_parts.append('        <h2 id="constructors">Constructors</h2>\n')
        html_parts.append(
            '        <p class="section-note">For each type in this module: inductive types '
            "list their declared constructors; opaque types list any local function whose name "
            "starts with <code>mk</code> and which returns a value of that type.</p>\n"
        )
        for t, entries in constructors_by_type:
            t_anchor = f"ctor-type-{html.escape(t.name)}-L{t.line_number}"
            kind_label = "inductive" if t.is_inductive else "opaque · mk*"
            type_anchor = f"type-{html.escape(t.name)}-L{t.line_number}"
            html_parts.append(f'        <div class="ctor-group" id="{t_anchor}">\n')
            html_parts.append(
                f'            <h3 class="ctor-group-header">'
                f'<a href="#{type_anchor}" class="ctor-type-link">{html.escape(t.name)}</a>'
                f' <span class="item-type">({kind_label})</span></h3>\n'
            )
            for e in entries:
                e_anchor = f"ctor-{html.escape(t.name)}-{html.escape(e['name'])}-L{e['line_number']}"
                if e["kind"] == "mk":
                    func: FunctionDoc = e["func"]
                    # h4 — nested under the per-type <h3 class="ctor-group-header">.
                    render_function_item(func, e_anchor, extra_classes="ctor-item", heading_tag="h4")
                else:
                    html_parts.append(f'        <div class="item ctor-item" id="{e_anchor}">\n')
                    html_parts.append('            <div class="item-header">\n')
                    html_parts.append(f'                <h4 class="item-name">{html.escape(e["name"])}</h4>\n')
                    html_parts.append(
                        '                <span class="badge badge-ctor"'
                        ' title="Data constructor of an inductive type.">constructor</span>\n'
                    )
                    html_parts.append("            </div>\n")
                    if e["comment"]:
                        html_parts.append(f'            <div class="comment">{html.escape(e["comment"])}</div>\n')
                    html_parts.append(f'            <div class="signature">{html.escape(e["type_sig"])}</div>\n')
                    html_parts.append("        </div>\n")
            html_parts.append("        </div>\n")

    if regular_functions:
        html_parts.append('        <h2 id="functions">Functions</h2>\n')
        for func in regular_functions:
            anchor = f"func-{html.escape(func.name)}-L{func.line_number}"
            render_function_item(func, anchor)

    if uninterpreted_functions:
        html_parts.append('        <h2 id="uninterpreted">Uninterpreted</h2>\n')
        html_parts.append(
            '        <p class="section-note">Functions declared as '
            "<code>def f ... = uninterpreted</code>: only their signature is known to the verifier; "
            "they have no body.</p>\n"
        )
        for func in uninterpreted_functions:
            anchor = f"func-{html.escape(func.name)}-L{func.line_number}"
            render_function_item(func, anchor)

    html_parts.append("""    </div>
</body>
</html>
""")

    html_content = "".join(html_parts)

    if output_path:
        with open(output_path, "w", encoding="utf-8") as out_file:
            out_file.write(html_content)

    return html_content


def generate_documentation(filename: str, output_path: str | None = None, source: str | None = None) -> str:
    """
    Generate HTML documentation for an Aeon source file.

    Args:
        filename: Path to the .ae file
        output_path: Optional path to write the HTML file (default: same name with .html extension)
        source: Optional source code (if None, will read from filename)

    Returns:
        The generated HTML as a string
    """
    doc = extract_documentation(filename, source)

    if output_path is None:
        output_path = str(Path(filename).with_suffix(".html"))

    html_content = generate_html(doc, output_path)
    return html_content
