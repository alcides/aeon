"""Meta-programming code for optimization-related decorators."""

import csv
import io
from typing import NamedTuple
from aeon.decorators.api import Metadata, metadata_update
from aeon.sugar.program import Decorator, Definition, SApplication, STerm, SVar
from aeon.sugar.stypes import SType
from aeon.sugar.ast_helpers import st_int, st_float, st_top, st_bool
from aeon.sugar.parser import parse_type
from aeon.utils.name import Name, fresh_counter

from aeon.sugar.program import SIf, SLiteral


class Goal(NamedTuple):
    minimize: bool
    length: int
    function: Name
    # Discriminator for how the synthesizer should compute the fitness value
    # for this goal. ``"expression"`` (the default) evaluates the internal
    # fitness function and returns its numeric result. ``"cputime"`` measures
    # the CPU time consumed evaluating it. ``"energy"`` measures the energy
    # consumed evaluating it (via RAPL when available, otherwise a CPU-time
    # proxy). See ``aeon/synthesis/entrypoint.py``.
    kind: str = "expression"


class Example(NamedTuple):
    """A single ``@example(...)`` assertion attached to a function.

    ``function`` is the name of an internal nullary ``Bool`` binding that
    evaluates the assertion (used by the ``--test`` runner); ``text`` is a
    surface rendering kept for human-readable test reports.
    """

    function: Name
    text: str


def multi_objective_type(element: str, number_of_objectives: int) -> SType:
    """Return type for a multi-objective fitness function: the native ``Array``
    refined to hold exactly one element per objective.

    The per-objective errors are returned as the language's native array type
    (consistent across every multi-objective decorator), refined so its length
    equals the number of objectives ``N`` derived from the decorator's argument
    list. See issue #294.

    The refinement uses ``Array_size`` — the abstract ``size`` measure exposed
    by ``libraries/Array.ae`` under its module-qualified internal name. This is
    the name the measure carries in the typing context regardless of whether the
    program imports ``Array`` qualified or ``open``; it is resolved by
    ``bind_ids`` rather than the surface qualified-name pass (which runs before
    decorators expand).
    """
    return parse_type(f"{{v:(Array {element}) | Array_size v == {number_of_objectives}}}")


def make_optimizer(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
    typ: SType,
    minimize: bool,
    length: int = 1,
    kind: str = "expression",
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
    goal = Goal(minimize, length, function_name, kind)

    metadata = metadata_update(
        metadata,
        fun,
        {
            "goals": current_goals + [goal],
        },
    )
    return fun, [function], metadata


def minimize_int(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    assert len(decorator.macro_args) == 1, "minimize_int decorator expects a single argument"
    return make_optimizer(decorator.macro_args, fun, metadata, st_int, minimize=True)


def maximize_int(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    assert len(decorator.macro_args) == 1, "maximize_int decorator expects a single argument"
    return make_optimizer(decorator.macro_args, fun, metadata, st_int, minimize=False)


def minimize_float(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    assert len(decorator.macro_args) == 1, "minimize_float decorator expects a single argument"
    return make_optimizer(decorator.macro_args, fun, metadata, st_float, minimize=True)


def maximize_float(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    assert len(decorator.macro_args) == 1, "maximize_float decorator expects a single argument"
    return make_optimizer(decorator.macro_args, fun, metadata, st_float, minimize=False)


def cluster(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """Name a function that maps a candidate to its *vector representation*.

    Used only by the metric (``symetric``) backend: it clusters individuals --
    and measures the goal-independent distance between them -- by these vectors
    rather than by the candidates' raw outputs. The argument is an expression in
    the same form as ``@minimize_int`` (e.g. ``@cluster(scene shape)``); it is
    lifted into an internal nullary function whose name is recorded under the
    ``cluster`` metadata key. Other backends ignore it.
    """
    assert len(decorator.macro_args) == 1, "cluster decorator expects a single argument"
    function_name = Name(f"__internal__cluster_{fun.name}", fresh_counter.fresh())
    function = Definition(
        name=function_name,
        foralls=[],
        args=[],
        type=st_top,
        body=decorator.macro_args[0],
    )
    metadata = metadata_update(metadata, fun, {"cluster": function_name})
    return fun, [function], metadata


def multi_minimize_float(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """Minimize a fitness function that returns an ``(Array Float)`` of per-objective errors."""
    assert len(decorator.macro_args) == 2, "multi_minimize_float decorator expects two arguments"
    assert isinstance(decorator.macro_args[1], SLiteral)
    assert isinstance(decorator.macro_args[1].value, int), "multi_minimize_float decorator expects an integer argument"
    number_of_objectives = decorator.macro_args[1].value
    return make_optimizer(
        [decorator.macro_args[0]],
        fun,
        metadata,
        multi_objective_type("Float", number_of_objectives),
        minimize=True,
        length=number_of_objectives,
    )


def multi_minimize_int(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """Minimize a fitness function that returns an ``(Array Int)`` of per-objective errors."""
    assert len(decorator.macro_args) == 2, "multi_minimize_int decorator expects two arguments"
    assert isinstance(decorator.macro_args[1], SLiteral)
    assert isinstance(decorator.macro_args[1].value, int), "multi_minimize_int decorator expects an integer argument"
    number_of_objectives = decorator.macro_args[1].value
    return make_optimizer(
        [decorator.macro_args[0]],
        fun,
        metadata,
        multi_objective_type("Int", number_of_objectives),
        minimize=True,
        length=number_of_objectives,
    )


def error_fitness(
    decorator: Decorator, fun: Definition, metadata: Metadata
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects one argument .

    It does not modify the original definition. It makes sure that
    the error fitness in case of any exception during the synthesis is the one defined in the argument
    """
    assert len(decorator.macro_args) == 1

    aux_dict = {"error_fitness": decorator.macro_args[0]}
    metadata = metadata_update(metadata, fun, aux_dict)

    return fun, [], metadata


def disable_control_flow(
    decorator: Decorator, fun: Definition, metadata: Metadata
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects zero arguments .

    It does not modify the original definition. It makes sure that
    the control flow grammar nodes are allowed during synthesis
    """
    assert len(decorator.macro_args) == 0

    aux_dict = {"disable_control_flow": True}
    metadata = metadata_update(metadata, fun, aux_dict)

    return fun, [], metadata


def allow_recursion(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects a zero argument .

    It does not modify the original definition. It makes sure that
    recursion can be used during synthesis
    """
    assert len(decorator.macro_args) == 0

    aux_dict = {"recursion": True}
    metadata = metadata_update(metadata, fun, aux_dict)

    return fun, [], metadata


def property_test(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """Marks a ``Bool``-returning function as a property to be checked by the
    property-based testing runner (``--test``).

    The function's arguments are the universally-quantified inputs; their types
    (including refinements, which act as preconditions) drive automatic input
    generation by reusing the synthesis grammar machinery. The definition is
    left unchanged — this decorator only records metadata.

    Usage::

        @property
        def prop_rev (l : List) : Bool { eq (reverse (reverse l)) l }

        @property(1000)            # optional: number of random samples
        def prop_abs (x : Int) : Bool { abs x >= 0 }
    """
    samples: int | None = None
    if decorator.macro_args:
        assert len(decorator.macro_args) == 1, "property decorator expects at most one (integer) argument"
        arg = decorator.macro_args[0]
        assert isinstance(arg, SLiteral) and isinstance(arg.value, int), (
            "property decorator's argument must be an integer literal (the number of samples)"
        )
        samples = arg.value
    metadata = metadata_update(metadata, fun, {"property": {"samples": samples}})
    return fun, [], metadata


def example(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """Attach a concrete input/output ``example`` to a function.

    The single argument is a ``Bool``-valued assertion about the decorated
    function — typically an equality between a fully-applied call and its
    expected result::

        # Absolute value of an integer.
        @example(abs (0 - 3) == 3)
        @example(abs 5 == 5)
        def abs (x : Int) : Int { if x < 0 then 0 - x else x }

    A single ``@example`` plays three roles:

    * **Documentation** — it is rendered alongside the function in the HTML
      docs (``--doc``), giving every function a worked, machine-checked example.
    * **Test case** (``--test``) — the assertion is evaluated and must hold;
      a false (or crashing) example is reported as a failure, like a unit test.
    * **Synthesis goal** — it contributes a fitness objective minimizing
      ``if assertion then 0 else 1``, so a fitness-based synthesizer searching
      for a body (a ``?`` hole) is driven to satisfy every example
      (programming-by-example). Examples compose with each other and with the
      other ``@minimize``/``@maximize`` objectives.

    The decorated definition is left unchanged; the decorator only records
    metadata and appends internal helper bindings.
    """
    assert len(decorator.macro_args) == 1, "example decorator expects a single Bool expression"
    assertion = decorator.macro_args[0]

    # (1) An internal nullary Bool binding holding the raw assertion. The
    # ``--test`` runner locates it by name and requires it to evaluate to True.
    current = metadata.get(fun.name, {}).get("examples", [])
    test_name = Name(f"__internal__example_{fun.name}_{len(current)}", fresh_counter.fresh())
    test_fn = Definition(name=test_name, foralls=[], args=[], type=st_bool, body=assertion)

    try:
        from aeon.utils.pprint import pretty_print_sterm

        text = pretty_print_sterm(assertion)
    except Exception:
        text = repr(assertion)

    metadata = metadata_update(metadata, fun, {"examples": current + [Example(test_name, text)]})

    # (2) If the assertion is a numeric ``f(lits) == lit``, also record it as a
    # training-data point so the decision-tree synthesizer (``-s decision_tree``)
    # can learn a function from the examples directly.
    point = _extract_example_point(assertion, fun.name)
    if point is not None:
        current_data = metadata.get(fun.name, {}).get("training_data", [])
        metadata = metadata_update(metadata, fun, {"training_data": current_data + [point]})

    # (3) A synthesis goal: minimize (if assertion then 0 else 1), so a
    # fitness-based synthesizer is rewarded for satisfying the example.
    goal_body = SIf(assertion, SLiteral(0, st_int), SLiteral(1, st_int))
    fun, extra, metadata = make_optimizer([goal_body], fun, metadata, st_int, minimize=True)
    return fun, [test_fn] + extra, metadata


def prompt(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    "Keeps track of the prompt that should be used in LLM-based synthesis"
    assert len(decorator.macro_args) == 1
    assert isinstance(decorator.macro_args[0], SLiteral) and isinstance(decorator.macro_args[0].value, str)
    val = decorator.macro_args[0].value
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
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """Decorator that accepts inline CSV data as a string.

    Each row is a data point where the last column is the expected output
    and preceding columns are function arguments. Minimizes sum of absolute errors.

    Usage: @csv_data("1.0,2.0,3.0\\n4.0,5.0,12.0")
    """
    assert len(decorator.macro_args) == 1, "csv_data decorator expects a single string argument"
    assert isinstance(decorator.macro_args[0], SLiteral) and isinstance(decorator.macro_args[0].value, str), (
        "csv_data decorator expects a string literal"
    )

    rows = _parse_csv_rows(decorator.macro_args[0].value)
    body = _build_csv_fitness_body(rows, fun.name)
    current_data = metadata.get(fun.name, {}).get("training_data", [])
    metadata = metadata_update(metadata, fun, {"training_data": current_data + rows})
    return make_optimizer([body], fun, metadata, st_float, minimize=True)


def csv_file(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """Decorator that accepts a CSV filename.

    Reads the file and behaves like csv_data: each row is a data point where
    the last column is the expected output and preceding columns are function arguments.
    Minimizes sum of absolute errors.

    Usage: @csv_file("data.csv")
    """
    assert len(decorator.macro_args) == 1, "csv_file decorator expects a single string argument"
    assert isinstance(decorator.macro_args[0], SLiteral) and isinstance(decorator.macro_args[0].value, str), (
        "csv_file decorator expects a string literal"
    )

    filename = decorator.macro_args[0].value
    with open(filename) as f:
        text = f.read()

    rows = _parse_csv_rows(text)
    body = _build_csv_fitness_body(rows, fun.name)
    current_data = metadata.get(fun.name, {}).get("training_data", [])
    metadata = metadata_update(metadata, fun, {"training_data": current_data + rows})
    return make_optimizer([body], fun, metadata, st_float, minimize=True)


def _call_arg_literals(term: STerm, fun_name: Name) -> list[float] | None:
    """If ``term`` is a fully-applied call ``fun_name(lit1)...(litN)`` with numeric
    literal arguments, return ``[lit1, ..., litN]`` (left-to-right); else ``None``.

    Bool literals are rejected (``True``/``False`` are ``int`` instances in
    Python but are not numeric training features)."""
    args: list[float] = []
    current = term
    while isinstance(current, SApplication):
        arg = current.arg
        if not isinstance(arg, SLiteral) or isinstance(arg.value, bool) or not isinstance(arg.value, (int, float)):
            return None
        args.append(float(arg.value))
        current = current.fun
    if not isinstance(current, SVar) or current.name.name != fun_name.name:
        return None
    args.reverse()
    return args


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
    if not isinstance(rhs, SLiteral) or isinstance(rhs.value, bool) or not isinstance(rhs.value, (int, float)):
        return None
    expected = float(rhs.value)

    args = _call_arg_literals(lhs, fun_name)
    if args is None:
        return None
    return args + [expected]


def _extract_example_point(assertion: STerm, fun_name: Name) -> list[float] | None:
    """Try to extract a training data point from an ``@example`` assertion.

    Looks for an equality ``fun_name(lit1)...(litN) == expected_lit`` (in either
    order) with numeric literals, and returns ``[lit1, ..., litN, expected_lit]``.
    Any other shape (Bool examples, non-literal arguments, other operators)
    yields ``None`` — so it composes with, but does not require, the decision-tree
    synthesizer.
    """
    if not (isinstance(assertion, SApplication) and isinstance(assertion.fun, SApplication)):
        return None
    op = assertion.fun.fun
    if not isinstance(op, SVar) or op.name.name != "==":
        return None
    lhs = assertion.fun.arg
    rhs = assertion.arg
    # The expected value may be on either side: (call == lit) or (lit == call).
    for call_side, lit_side in ((lhs, rhs), (rhs, lhs)):
        if not isinstance(lit_side, SLiteral) or isinstance(lit_side.value, bool):
            continue
        if not isinstance(lit_side.value, (int, float)):
            continue
        args = _call_arg_literals(call_side, fun_name)
        if args is not None:
            return args + [float(lit_side.value)]
    return None


def _store_training_point(expr: STerm, fun: Definition, metadata: Metadata) -> Metadata:
    """If the expression matches f(args) - expected, store as training data."""
    point = _extract_training_point(expr, fun.name)
    if point is not None:
        current_data = metadata.get(fun.name, {}).get("training_data", [])
        metadata = metadata_update(metadata, fun, {"training_data": current_data + [point]})
    return metadata


def minimize(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """Minimize decorator that also extracts training data when possible.

    Usage: @minimize(f(1.0, 2.0) - 3.0)

    Creates a fitness goal (like minimize_float) and, if the expression matches
    the pattern f(literal_args) - expected_literal, also stores a training data
    point for the decision tree synthesizer.
    """
    assert len(decorator.macro_args) == 1, "minimize decorator expects a single argument"
    metadata = _store_training_point(decorator.macro_args[0], fun, metadata)
    return make_optimizer(decorator.macro_args, fun, metadata, st_float, minimize=True)


def maximize(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """Maximize decorator converted to minimize, also extracts training data.

    Usage: @maximize(3.0 - f(1.0, 2.0))

    Internally converts to minimizing the negated expression (0 - expr).
    If the original expression matches the pattern f(literal_args) - expected_literal,
    stores a training data point for the decision tree synthesizer.
    """
    assert len(decorator.macro_args) == 1, "maximize decorator expects a single argument"
    # Extract training data from the original expression
    metadata = _store_training_point(decorator.macro_args[0], fun, metadata)
    # Convert maximize(expr) to minimize(0 - expr)
    negated = _binop("-", SLiteral(0.0, st_float), decorator.macro_args[0])
    return make_optimizer([negated], fun, metadata, st_float, minimize=True)


def minimize_cputime(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """Adds CPU time of the given expression as a synthesis objective.

    Usage: ``@minimize_cputime(fun 42)``.

    The expression is typically a call to the decorated function. During
    synthesis, the synthesizer evaluates the candidate program against this
    expression and the CPU time consumed (in seconds) is contributed as a
    fitness value to be minimized. Composes with other objectives. The value
    produced by the expression itself is ignored, so its type is unconstrained.
    """
    assert len(decorator.macro_args) == 1, "minimize_cputime decorator expects a single argument"
    return make_optimizer(decorator.macro_args, fun, metadata, st_top, minimize=True, kind="cputime")


def minimize_energy(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """Adds energy consumption of the given expression as a synthesis objective.

    Usage: @minimize_energy(fun 42)

    The expression is typically a call to the decorated function. During
    synthesis, the synthesizer evaluates the candidate program against this
    expression and the energy consumed (in joules) is contributed as a fitness
    value to be minimized. When the optional ``pyRAPL`` package is installed
    and the platform provides Intel RAPL counters, real hardware readings are
    used; otherwise a CPU-time proxy is used (energy = cpu_time * default_power)
    so the search signal is still meaningful. Composes with other objectives.
    The value produced by the expression itself is ignored, so its type is
    unconstrained.
    """
    assert len(decorator.macro_args) == 1, "minimize_energy decorator expects a single argument"
    return make_optimizer(decorator.macro_args, fun, metadata, st_top, minimize=True, kind="energy")
