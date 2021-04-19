from typing import Optional, Tuple


all_ops = [
    ("==", ("a", "a", "Bool")),
    ("!=", ("a", "a", "Bool")),
    ("<", ("Int", "Int", "Bool")),
    (">", ("Int", "Int", "Bool")),
    ("<=", ("Int", "Int", "Bool")),
    (">=", ("Int", "Int", "Bool")),
    ("-->", ("Bool", "Bool", "Bool")),
    ("&&", ("Bool", "Bool", "Bool")),
    ("||", ("Bool", "Bool", "Bool")),
    ("*", ("Int", "Int", "Int")),
    ("+", ("Int", "Int", "Int")),
    ("/", ("Int", "Int", "Int")),
    ("-", ("Int", "Int", "Int")),
    ("%", ("Int", "Int", "Int")),
    ("!", ("Bool", "Bool")),
]


ops = [x[0] for x in all_ops]


def get_type_of(name: str) -> Optional[Tuple[str, str, str]]:
    for (op, t) in all_ops:
        if op == name:
            return t
    return None
