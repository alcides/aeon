"""Meta-programming code for optimization-related decorators."""

import csv
import io
from typing import NamedTuple
from aeon.decorators.api import Metadata, metadata_update
from aeon.sugar.program import Definition, SApplication, STerm, SVar
from aeon.sugar.stypes import STypeConstructor
from aeon.sugar.ast_helpers import st_int, st_float
from aeon.utils.name import Name, fresh_counter

from aeon.sugar.program import SLiteral


def raise_decorator_error(name: str) -> None:
    raise Exception(f"Exception in decorator named {name}.")


class Goal(NamedTuple):
    minimize: bool
    length: int
    function: Name


def make_optimizer(
    args: list[STerm], fun: Definition, metadata: Metadata, typ: STypeConstructor, minimize: bool, length: int = 1
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects a single argument (the body of the definition).

    It does not modify the original definition, but appends a new
    definition to the program. This new definition has the name
    "_fitness_function", prefixed by the original definition's name
    """
    current_goals = metadata.get(fun.name, {}).get("goals", [])
    minimize_name = "minimize" if minimize else "maximize"
    function_name = Name(f"__internal__{minimize_name}_{fun.name}_{len(current_goals)}", fresh_counter.fresh())
    function = Definition(
        name=function_name,
        foralls=[],
        args=[],
        type=typ,
        body=args[0],
    )
    goal = Goal(minimize, length, function_name)

    metadata = metadata_update(
        metadata,
        fun,
        {
            "goals": current_goals + [goal],
        },
    )
    return fun, [function], metadata


def minimize_int(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    assert len(args) == 1, "minimize_int decorator expects a single argument"
    return make_optimizer(args, fun, metadata, st_int, minimize=True)


def maximize_int(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    assert len(args) == 1, "maximize_int decorator expects a single argument"
    return make_optimizer(args, fun, metadata, st_int, minimize=False)


def minimize_float(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    assert len(args) == 1, "minimize_float decorator expects a single argument"
    return make_optimizer(args, fun, metadata, st_float, minimize=True)


def maximize_float(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    assert len(args) == 1, "maximize_float decorator expects a single argument"
    return make_optimizer(args, fun, metadata, st_float, minimize=False)


def multi_minimize_float(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects a single argument (the body of the definition)."""
    assert (
        len(
            args,
        )
        == 1
    ), "multi_minimize_float decorator expects a single argument"
    assert isinstance(args[1], SLiteral)
    assert isinstance(args[1].value, int), "multi_minimize_float decorator expects an integer argument"
    number_of_objectives = args[1].value
    return make_optimizer(
        args, fun, metadata, STypeConstructor(Name("List", 0)), minimize=True, length=number_of_objectives
    )


def hide(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects more than zero arguments.

    It does not modify the original definition. It makes sure that no
    grammar nodes are generated from the var names passed as arguments.
    """
    assert len(args) != 0

    # TODO How can I verify if the function is in the context?
    def get_var_name(arg):
        if isinstance(arg, SVar):
            return arg.name
        else:
            raise_decorator_error("hide")

    # rethink this
    aux_dict = {"hide": [get_var_name(arg) for arg in args]}
    metadata = metadata_update(metadata, fun, aux_dict)

    return fun, [], metadata


def hide_types(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects more than zero arguments.

    It does not modify the original definition. It makes sure that no
    grammar nodes are generated from the var names passed as arguments.
    """
    assert len(args) != 0

    # TODO How can I verify if the function is in the context?
    def get_var_name(arg):
        if isinstance(arg, SVar):
            return arg.name
        else:
            raise_decorator_error("hide_types")

    # rethink this
    aux_dict = {"hide_types": [get_var_name(arg) for arg in args]}
    metadata = metadata_update(metadata, fun, aux_dict)

    return fun, [], metadata


def error_fitness(
    args: list[STerm], fun: Definition, metadata: Metadata
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects one argument .

    It does not modify the original definition. It makes sure that
    the error fitness in case of any exception during the synthesis is the one defined in the argument
    """
    assert len(args) == 1

    aux_dict = {"error_fitness": args[0]}
    metadata = metadata_update(metadata, fun, aux_dict)

    return fun, [], metadata


def disable_control_flow(
    args: list[STerm], fun: Definition, metadata: Metadata
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects zero arguments .

    It does not modify the original definition. It makes sure that
    the control flow grammar nodes are allowed during synthesis
    """
    assert len(args) == 0

    aux_dict = {"disable_control_flow": True}
    metadata = metadata_update(metadata, fun, aux_dict)

    return fun, [], metadata


def allow_recursion(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects a zero argument .

    It does not modify the original definition. It makes sure that
    recursion can be used during synthesis
    """
    assert len(args) == 0

    aux_dict = {"recursion": True}
    metadata = metadata_update(metadata, fun, aux_dict)

    return fun, [], metadata


def prompt(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    "Keeps track of the prompt that should be used in LLM-based synthesis"
    assert len(args) == 1
    assert isinstance(args[0], SLiteral) and isinstance(args[0].value, str)
    val = args[0].value
    metadata = metadata_update(metadata, fun, {"prompt": val})

    return fun, [], metadata


def _binop(op: str, left: STerm, right: STerm) -> STerm:
    """Build a binary operation AST node: (op left right)."""
    return SApplication(SApplication(SVar(Name(op, 0)), left), right)


def _squared(expr: STerm) -> STerm:
    """Build expr * expr (squared error)."""
    return _binop("*", expr, expr)


def _parse_csv_rows(text: str) -> list[list[float]]:
    """Parse CSV text into a list of rows of floats."""
    # Handle escaped newlines from string literals
    text = text.replace("\\n", "\n")
    reader = csv.reader(io.StringIO(text.strip()))
    rows = []
    for row in reader:
        if not row or all(cell.strip() == "" for cell in row):
            continue
        rows.append([float(cell.strip()) for cell in row])
    return rows


def _build_csv_fitness_body(rows: list[list[float]], fun_name: Name) -> STerm:
    """Build the fitness body: sum of abs(f(x1,...,xn) - expected) for each row."""
    assert len(rows) > 0, "CSV data must contain at least one row"
    n_cols = len(rows[0])
    assert n_cols >= 2, "CSV data must have at least 2 columns (inputs + expected output)"
    for i, row in enumerate(rows):
        assert len(row) == n_cols, f"CSV row {i} has {len(row)} columns, expected {n_cols}"

    error_terms = []
    for row in rows:
        inputs = row[:-1]
        expected = row[-1]

        # Build f(x1)(x2)...(xn)
        call: STerm = SVar(fun_name)
        for val in inputs:
            call = SApplication(call, SLiteral(val, st_float))

        # (call - expected)^2
        diff = _binop("-", call, SLiteral(expected, st_float))
        error_terms.append(_squared(diff))

    # Sum all error terms
    total = error_terms[0]
    for term in error_terms[1:]:
        total = _binop("+", total, term)

    return total


def csv_data(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """Decorator that accepts inline CSV data as a string.

    Each row is a data point where the last column is the expected output
    and preceding columns are function arguments. Minimizes sum of absolute errors.

    Usage: @csv_data("1.0,2.0,3.0\\n4.0,5.0,12.0")
    """
    assert len(args) == 1, "csv_data decorator expects a single string argument"
    assert isinstance(args[0], SLiteral) and isinstance(args[0].value, str), (
        "csv_data decorator expects a string literal"
    )

    rows = _parse_csv_rows(args[0].value)
    body = _build_csv_fitness_body(rows, fun.name)
    current_data = metadata.get(fun.name, {}).get("training_data", [])
    metadata = metadata_update(metadata, fun, {"training_data": current_data + rows})
    return make_optimizer([body], fun, metadata, st_float, minimize=True)


def csv_file(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """Decorator that accepts a CSV filename.

    Reads the file and behaves like csv_data: each row is a data point where
    the last column is the expected output and preceding columns are function arguments.
    Minimizes sum of absolute errors.

    Usage: @csv_file("data.csv")
    """
    assert len(args) == 1, "csv_file decorator expects a single string argument"
    assert isinstance(args[0], SLiteral) and isinstance(args[0].value, str), (
        "csv_file decorator expects a string literal"
    )

    filename = args[0].value
    with open(filename) as f:
        text = f.read()

    rows = _parse_csv_rows(text)
    body = _build_csv_fitness_body(rows, fun.name)
    current_data = metadata.get(fun.name, {}).get("training_data", [])
    metadata = metadata_update(metadata, fun, {"training_data": current_data + rows})
    return make_optimizer([body], fun, metadata, st_float, minimize=True)


def _extract_training_point(expr: STerm, fun_name: Name) -> list[float] | None:
    """Try to extract a training data point from a minimize expression.

    Looks for pattern: (fun_name(lit1)(lit2)...(litN)) - expected_lit
    Returns [lit1, ..., litN, expected_lit] or None if pattern doesn't match.
    """
    # Check for (- lhs rhs) pattern
    if not isinstance(expr, SApplication):
        return None
    if not isinstance(expr.fun, SApplication):
        return None
    minus_op = expr.fun.fun
    if not isinstance(minus_op, SVar) or minus_op.name.name != "-":
        return None

    lhs = expr.fun.arg  # f(x1)(x2)...(xn)
    rhs = expr.arg  # expected

    # Extract expected value
    if not isinstance(rhs, SLiteral) or not isinstance(rhs.value, (int, float)):
        return None
    expected = float(rhs.value)

    # Extract function call arguments (built right-to-left via currying)
    args: list[float] = []
    current = lhs
    while isinstance(current, SApplication):
        arg = current.arg
        if not isinstance(arg, SLiteral) or not isinstance(arg.value, (int, float)):
            return None
        args.append(float(arg.value))
        current = current.fun

    # Verify it's calling the right function
    if not isinstance(current, SVar) or current.name.name != fun_name.name:
        return None

    args.reverse()
    return args + [expected]


def _store_training_point(expr: STerm, fun: Definition, metadata: Metadata) -> Metadata:
    """If the expression matches f(args) - expected, store as training data."""
    point = _extract_training_point(expr, fun.name)
    if point is not None:
        current_data = metadata.get(fun.name, {}).get("training_data", [])
        metadata = metadata_update(metadata, fun, {"training_data": current_data + [point]})
    return metadata


def minimize(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """Minimize decorator that also extracts training data when possible.

    Usage: @minimize(f(1.0, 2.0) - 3.0)

    Creates a fitness goal (like minimize_float) and, if the expression matches
    the pattern f(literal_args) - expected_literal, also stores a training data
    point for the decision tree synthesizer.
    """
    assert len(args) == 1, "minimize decorator expects a single argument"
    metadata = _store_training_point(args[0], fun, metadata)
    return make_optimizer(args, fun, metadata, st_float, minimize=True)


def maximize(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """Maximize decorator converted to minimize, also extracts training data.

    Usage: @maximize(3.0 - f(1.0, 2.0))

    Internally converts to minimizing the negated expression (0 - expr).
    If the original expression matches the pattern f(literal_args) - expected_literal,
    stores a training data point for the decision tree synthesizer.
    """
    assert len(args) == 1, "maximize decorator expects a single argument"
    # Extract training data from the original expression
    metadata = _store_training_point(args[0], fun, metadata)
    # Convert maximize(expr) to minimize(0 - expr)
    negated = _binop("-", SLiteral(0.0, st_float), args[0])
    return make_optimizer([negated], fun, metadata, st_float, minimize=True)
