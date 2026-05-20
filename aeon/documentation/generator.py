"""AeonDoc generator - extracts documentation from Aeon source files and generates HTML."""

from __future__ import annotations

import html
from dataclasses import dataclass
from pathlib import Path

from aeon.sugar.program import Program, Decorator
from aeon.sugar.parser import parse_main_program
from aeon.sugar.bind import bind_program
from aeon.sugar.stypes import SType


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


def format_type(stype: SType) -> str:
    """Format a type for display."""
    return str(stype)


def format_decorator(dec: Decorator) -> str:
    """Format a decorator for display."""
    return repr(dec)


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

        args_str = [str(arg) for arg in type_decl.args]
        rforalls_formatted = [(str(n), format_type(s)) for n, s in type_decl.rforalls]

        types.append(
            TypeDoc(
                name=str(type_decl.name),
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

        args_str = [str(arg) for arg in inductive.args]
        rforalls_formatted = [(str(n), format_type(s)) for n, s in inductive.rforalls]

        constructors = []
        for cons in inductive.constructors:
            cons_line = cons.loc.start[0] if hasattr(cons.loc, "start") else 0
            cons_comment = find_preceding_comment(comments, cons_line)
            constructors.append(
                ConstructorDoc(
                    name=str(cons.name),
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
                    name=str(meas.name),
                    type_sig=format_type(meas.type),
                    comment=meas_comment,
                    line_number=meas_line,
                )
            )

        types.append(
            TypeDoc(
                name=str(inductive.name),
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
        comment = find_preceding_comment(comments, line_num)

        args_formatted = [(str(n), format_type(t)) for n, t in defn.args]
        decorators_formatted = [format_decorator(dec) for dec in defn.decorators]
        foralls_formatted = [(str(n), str(k)) for n, k in defn.foralls]
        rforalls_formatted = [(str(n), format_type(s)) for n, s in defn.rforalls]

        functions.append(
            FunctionDoc(
                name=str(defn.name),
                type_sig=format_type(defn.type),
                args=args_formatted,
                decorators=decorators_formatted,
                comment=comment,
                line_number=line_num,
                foralls=foralls_formatted,
                rforalls=rforalls_formatted,
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
            box-shadow: 0 2px 8px rgba(0,0,0,0.1);
            border-radius: 8px;
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
            overflow-x: auto;
            border-radius: 4px;
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
        .toc h2 {{
            margin-top: 0;
            font-size: 1.3em;
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
        html_parts.append("            <h3>Imports</h3>\n")
        for imp in doc.imports:
            html_parts.append(f"            <code>{html.escape(imp)}</code>\n")
        html_parts.append("        </div>\n")

    html_parts.append('        <div class="toc">\n')
    html_parts.append("            <h2>Table of Contents</h2>\n")
    html_parts.append("            <ul>\n")
    if doc.types:
        html_parts.append('                <li><a href="#types">Types</a>\n')
        html_parts.append("                    <ul>\n")
        for t in doc.types:
            html_parts.append(
                f'                        <li><a href="#type-{html.escape(t.name)}">{html.escape(t.name)}</a></li>\n'
            )
        html_parts.append("                    </ul>\n")
        html_parts.append("                </li>\n")
    if doc.functions:
        html_parts.append('                <li><a href="#functions">Functions</a>\n')
        html_parts.append("                    <ul>\n")
        for f in doc.functions:
            html_parts.append(
                f'                        <li><a href="#func-{html.escape(f.name)}">{html.escape(f.name)}</a></li>\n'
            )
        html_parts.append("                    </ul>\n")
        html_parts.append("                </li>\n")
    html_parts.append("            </ul>\n")
    html_parts.append("        </div>\n")

    if doc.types:
        html_parts.append('        <h2 id="types">Types</h2>\n')
        for type_doc in doc.types:
            html_parts.append(f'        <div class="item" id="type-{html.escape(type_doc.name)}">\n')
            html_parts.append('            <div class="item-header">\n')

            type_kind = "inductive" if type_doc.is_inductive else "type"
            html_parts.append(f'                <span class="item-name">{html.escape(type_doc.name)}</span>\n')
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

            if type_doc.is_inductive:
                if type_doc.constructors:
                    html_parts.append("            <h3>Constructors</h3>\n")
                    for cons in type_doc.constructors:
                        html_parts.append('            <div class="constructor">\n')
                        html_parts.append(
                            f'                <span class="constructor-name">{html.escape(cons.name)}</span> : <code>{html.escape(cons.type_sig)}</code>\n'
                        )
                        if cons.comment:
                            html_parts.append(
                                f'                <div class="comment">{html.escape(cons.comment)}</div>\n'
                            )
                        html_parts.append("            </div>\n")

                if type_doc.measures:
                    html_parts.append("            <h3>Measures</h3>\n")
                    for meas in type_doc.measures:
                        html_parts.append('            <div class="constructor">\n')
                        html_parts.append(
                            f'                <span class="constructor-name">{html.escape(meas.name)}</span> : <code>{html.escape(meas.type_sig)}</code>\n'
                        )
                        if meas.comment:
                            html_parts.append(
                                f'                <div class="comment">{html.escape(meas.comment)}</div>\n'
                            )
                        html_parts.append("            </div>\n")

            html_parts.append("        </div>\n")

    if doc.functions:
        html_parts.append('        <h2 id="functions">Functions</h2>\n')
        for func in doc.functions:
            html_parts.append(f'        <div class="item" id="func-{html.escape(func.name)}">\n')
            html_parts.append('            <div class="item-header">\n')
            html_parts.append(f'                <span class="item-name">{html.escape(func.name)}</span>\n')
            html_parts.append("            </div>\n")

            if func.decorators:
                html_parts.append('            <div class="decorators">\n')
                for dec in func.decorators:
                    html_parts.append(f'                <span class="decorator">{html.escape(dec)}</span>\n')
                html_parts.append("            </div>\n")

            if func.comment:
                html_parts.append(f'            <div class="comment">{html.escape(func.comment)}</div>\n')

            sig_parts = ["def", func.name]

            if func.foralls:
                for name, kind in func.foralls:
                    sig_parts.append(f"∀{name}:{kind}")

            if func.rforalls:
                for name, sort in func.rforalls:
                    sig_parts.append(f"∀<{name}:{sort} -> Bool>")

            if func.args:
                args_str = ", ".join([f"({n}: {t})" for n, t in func.args])
                sig_parts.append(args_str)

            sig_parts.append(":")
            sig_parts.append(func.type_sig)

            html_parts.append(f'            <div class="signature">{html.escape(" ".join(sig_parts))}</div>\n')

            html_parts.append("        </div>\n")

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
