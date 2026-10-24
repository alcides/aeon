"""Insert explicit delimiters for indented proof blocks only.

Aeon's expression grammar is whitespace-insensitive. Keeping insertion at line
ends preserves original line numbers and columns of user-written tokens.
"""

import re


def proof_layout(source: str) -> str:
    lines = source.splitlines(keepends=True)
    result: list[tuple[str, str, str]] = []
    stack: list[dict[str, int | None]] = []
    previous = None

    def split_comment(line):
        quoted = escaped = False
        for i, char in enumerate(line):
            if escaped:
                escaped = False
            elif char == "\\" and quoted:
                escaped = True
            elif char == '"':
                quoted = not quoted
            elif char == "#" and not quoted and not line[i:].startswith("#["):
                return line[:i], line[i:]
        return line, ""

    def append(index, text):
        code, comment, ending = result[index]
        result[index] = (code.rstrip() + text, comment, ending)

    for line in lines:
        ending = "\n" if line.endswith("\n") else ""
        code, comment = split_comment(line.rstrip("\r\n"))
        stripped = code.strip()
        if not stripped:
            result.append((code, comment, ending))
            continue
        indent = len(code) - len(code.lstrip())
        while stack and indent <= stack[-1]["parent"]:
            if previous is not None:
                append(previous, ")")
            stack.pop()
        if stack:
            block = stack[-1]
            if block["body"] is None:
                block["body"] = indent
            elif indent == block["body"] and not stripped.startswith("|"):
                if previous is not None and not result[previous][0].rstrip().endswith((";", "with")):
                    append(previous, ";")
        result.append((code, comment, ending))
        previous = len(result) - 1
        opens = bool(re.search(r"\b(by|calc)$", stripped))
        if stack and stripped.endswith("=>"):
            opens = True
        if opens:
            append(previous, " (")
            stack.append({"parent": indent, "body": None})
    while stack:
        if previous is not None:
            append(previous, ")")
        stack.pop()
    return "".join(code + (" " if comment and code else "") + comment + ending for code, comment, ending in result)
