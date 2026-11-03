"""Meta-programming code for optimization-related decorators."""

import csv
import io
from typing import NamedTuple
from aeon.core.multiplicity import M1
from aeon.decorators.api import Metadata, metadata_update
from aeon.sugar.program import Decorator, Definition, SAnnotation, SApplication, SLet, STerm, SVar, SQualifiedVar
from aeon.sugar.stypes import SRefinedType, SType, STypeConstructor
from aeon.sugar.ast_helpers import st_int, st_float, st_top, st_bool, st_string
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
    # proxy). ``"property"`` is a runtime objective backed by a fixed corpus;
    # its ``function`` identifies the property rather than a generated numeric
    # helper. ``"size"`` counts hole replacements in the definition identified
    # by ``function``, without evaluating it. See ``aeon/synthesis/entrypoint.py``.
    # ``"example"`` and ``"csv"`` preserve the source of zero-target error
    # goals, so satisfaction backends can validate them without guessing what
    # value an arbitrary optimization expression is supposed to attain.
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
    return parse_type(f"{{v:(Array {element}) | Array_size v = {number_of_objectives}}}")


def _is_native_array_type(typ: SType) -> bool:
    """True when ``typ`` is (a refinement of) the linear ``Array`` constructor."""
    base = typ.type if isinstance(typ, SRefinedType) else typ
    return isinstance(base, STypeConstructor) and base.name.name == "Array"


def _array_fitness_as_omega_float(array_expr: STerm, array_ty: SType) -> STerm:
    """Consume a linear ``Array`` fitness expression and re-export it as ``Float``.

    Top-level fitness helpers must be ``ω``-bindable (they sit unused in the
    main program and are only evaluated by substituting them as the program
    tail). ``Array`` is linear, so binding the raw expression at ``ω`` is
    rejected. We therefore:

    1. type-ascribe the user expression to the refined ``Array`` type;
    2. bind it at multiplicity ``1`` (consuming it exactly once);
    3. return it via ``native "arr"``, which yields the Python list at runtime
       while the helper's declared type stays the non-linear ``Float``.

    ``as_objective_vector`` then expands that list into one float per objective.
    """
    arr = Name("arr", fresh_counter.fresh())
    ascribed = SAnnotation(array_expr, array_ty)
    native_list = SApplication(SVar(Name("native", 0)), SLiteral("arr", st_string))
    return SLet(arr, ascribed, native_list, multiplicity=M1)


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
    function_name = Name(f"_fitness_{minimize_name}_{fun.name}_{len(current_goals)}", fresh_counter.fresh())
    if _is_native_array_type(typ):
        # Linear ``Array`` cannot be an unused top-level ``ω`` binding; wrap it
        # so the helper stays ``Float``-typed while still evaluating to a list.
        helper_type: SType = st_float
        helper_body = _array_fitness_as_omega_float(args[0], typ)
    else:
        helper_type = typ
        helper_body = args[0]
    function = Definition(
        name=function_name,
        foralls=[],
        args=[],
        type=helper_type,
        body=helper_body,
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
    metadata = _store_training_point(decorator.macro_args[0], fun, metadata)
    return make_optimizer(decorator.macro_args, fun, metadata, st_int, minimize=True)


def require(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """A hard Boolean synthesis constraint, currently supported by CP-SAT.

    Keep the helper numeric so existing goal metadata, display, and evaluator
    protocols remain valid. A supporting backend requires its value to be zero,
    independently of the optimization objective. Unsupported backends reject
    this goal explicitly rather than treating it as a weighted penalty.
    """
    assert len(decorator.macro_args) == 1, "require expects one Boolean expression"
    violation = SIf(decorator.macro_args[0], SLiteral(0, st_int), SLiteral(1, st_int))
    return make_optimizer([violation], fun, metadata, st_int, minimize=True, kind="constraint")


def maximize_int(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    assert len(decorator.macro_args) == 1, "maximize_int decorator expects a single argument"
    metadata = _store_training_point(decorator.macro_args[0], fun, metadata, maximize=True)
    return make_optimizer(decorator.macro_args, fun, metadata, st_int, minimize=False)


def minimize_float(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    assert len(decorator.macro_args) == 1, "minimize_float decorator expects a single argument"
    metadata = _store_training_point(decorator.macro_args[0], fun, metadata)
    return make_optimizer(decorator.macro_args, fun, metadata, st_float, minimize=True)


def maximize_float(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    assert len(decorator.macro_args) == 1, "maximize_float decorator expects a single argument"
    metadata = _store_training_point(decorator.macro_args[0], fun, metadata, maximize=True)
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
    function_name = Name(f"_cluster_{fun.name}", fresh_counter.fresh())
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
    generation by reusing the synthesis grammar machinery. When the property
    directly mentions a function with a synthesis hole, runtime-fitness backends
    also minimize the number of failures over one deterministic corpus generated
    before search. The definition is left unchanged — this decorator only records
    metadata.

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
    test_name = Name(f"_example_{fun.name}_{len(current)}", fresh_counter.fresh())
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

    # (2b) If the assertion is an I/O equality ``f(lits) == lit`` over scalar
    # literals (int/string/bool, in any order), record the concrete input/output
    # pair so example-driven (PBE) synthesizers -- e.g. ``afta`` over a string
    # DSL -- can build a tree automaton consistent with all the examples. Unlike
    # ``training_data`` (numeric only, for the decision tree) this keeps string
    # I/O, which is what the BLAZE-style string/matrix benchmarks need.
    io = _extract_io_example(assertion, fun.name)
    # Preserve general constructor trees separately from Contata's legacy
    # flattened list encoding. Only registered, fully applied constructors
    # and scalar literals are decoded; arbitrary native code is never run.
    constructor_io = _extract_io_example(assertion, fun.name, decode=_constructor_literal_value)
    if constructor_io is not None:
        current_constructor_io = metadata.get(fun.name, {}).get("constructor_io_examples", [])
        metadata = metadata_update(
            metadata,
            fun,
            {
                "constructor_io_examples": current_constructor_io + [constructor_io],
                "io_params": [n for (n, _t) in fun.args],
            },
        )
    if io is not None:
        current_io = metadata.get(fun.name, {}).get("io_examples", [])
        metadata = metadata_update(metadata, fun, {"io_examples": current_io + [io]})
        # The positional value-parameter names, so the synthesizer can bind each
        # example's inputs when it evaluates a candidate body.
        if "io_params" not in metadata.get(fun.name, {}):
            metadata = metadata_update(metadata, fun, {"io_params": [n for (n, _t) in fun.args]})
    else:
        # Hygiene: help authors who ``open List`` then shadow ``length`` — the
        # assertion may have been rebound to ``List_length`` and I/O extraction
        # failed. Surface a soft warning via metadata for tooling; synthesis
        # backends already error clearly when ``io_examples`` is empty.
        metadata = metadata_update(
            metadata,
            fun,
            {
                "example_io_miss": metadata.get(fun.name, {}).get("example_io_miss", []) + [text],
            },
        )

    # (3) A synthesis goal: minimize (if assertion then 0 else 1), so a
    # fitness-based synthesizer is rewarded for satisfying the example.
    goal_body = SIf(assertion, SLiteral(0, st_int), SLiteral(1, st_int))
    fun, extra, metadata = make_optimizer([goal_body], fun, metadata, st_int, minimize=True, kind="example")
    return fun, [test_fn] + extra, metadata


def bounded_cnf(
    decorator: Decorator, fun: Definition, metadata: Metadata
) -> tuple[Definition, list[Definition], Metadata]:
    """Declare a hard upper bound on normalized CNF clauses, independent of fitness."""
    from aeon.errors import InvalidDecoratorArgumentError

    args = decorator.macro_args
    if len(args) != 1 or not isinstance(args[0], SLiteral) or type(args[0].value) is not int or args[0].value < 0:
        raise InvalidDecoratorArgumentError(decorator, "expected one nonnegative integer literal clause bound")
    if "bounded_cnf" in metadata.get(fun.name, {}):
        raise InvalidDecoratorArgumentError(decorator, "duplicate clause bound")
    return fun, [], metadata_update(metadata, fun, {"bounded_cnf": args[0].value})


def _binop(op: str, left: STerm, right: STerm) -> STerm:
    """Build a binary operation AST node: (op left right)."""
    return SApplication(SApplication(SVar(Name(op, 0)), left), right)


def _squared(expr: STerm) -> STerm:
    """Build expr * expr (squared error)."""
    return _binop("*", expr, expr)


def _csv_scalar_type(ty: SType) -> SType:
    """Read columns using the declaration, retaining Int/Bool/String values."""
    while isinstance(ty, SRefinedType):
        ty = ty.type
    scalar_types = {"Int": st_int, "Float": st_float, "Bool": st_bool, "String": st_string}
    if isinstance(ty, STypeConstructor) and not ty.args and ty.name.name in scalar_types:
        return scalar_types[ty.name.name]
    raise ValueError(f"CSV specifications require scalar Int/Float/Bool/String columns, got {ty}")


def _parse_csv_rows(text: str, column_types: list[SType]) -> list[list]:
    """Parse both CSV decorators with the same arity and scalar-type checks."""
    from math import isfinite

    rows = []
    reader = csv.reader(io.StringIO(text.replace("\\n", "\n")))
    for line, row in enumerate(reader, 1):
        if not row or (st_string not in column_types and all(cell.strip() == "" for cell in row)):
            continue
        if len(row) != len(column_types):
            raise ValueError(f"CSV row {line} has {len(row)} columns, expected {len(column_types)}")
        values = []
        for column, (cell, ty) in enumerate(zip(row, column_types), 1):
            value: str | bool | int | float
            try:
                if ty == st_string:
                    value = cell
                elif ty == st_bool:
                    if cell.strip().lower() not in ("true", "false"):
                        raise ValueError("expected true or false")
                    value = cell.strip().lower() == "true"
                elif ty == st_int:
                    value = int(cell.strip())
                else:
                    value = float(cell.strip())
                    if not isfinite(value):
                        raise ValueError("expected a finite number")
            except ValueError as exc:
                raise ValueError(f"CSV row {line}, column {column}: invalid {ty}: {cell!r}") from exc
            values.append(value)
        rows.append(values)
    if not rows:
        raise ValueError("CSV data must contain at least one row")
    return rows


def _csv_specification(text: str, fun: Definition, metadata: Metadata) -> tuple[Definition, list[Definition], Metadata]:
    """Expose typed I/O to learners and retain CSV's runtime loss objective.

    Numeric outputs use squared error, preserving regression semantics. Bool
    and String outputs use a count of mismatches, whose exact-fit target is
    likewise zero. Only wholly numeric rows become regression training data.
    """
    columns = [_csv_scalar_type(ty) for _, ty in fun.args] + [_csv_scalar_type(fun.type)]
    rows = _parse_csv_rows(text, columns)
    numeric_output = columns[-1] in (st_int, st_float)
    fitness_type = columns[-1] if numeric_output else st_int
    errors: list[STerm] = []
    for row in rows:
        call: STerm = SVar(fun.name)
        for value, ty in zip(row[:-1], columns[:-1]):
            call = SApplication(call, SLiteral(value, ty))
        expected = SLiteral(row[-1], columns[-1])
        if numeric_output:
            errors.append(_squared(_binop("-", call, expected)))
        else:
            errors.append(SIf(_binop("==", call, expected), SLiteral(0, st_int), SLiteral(1, st_int)))
    total = errors[0]
    for error in errors[1:]:
        total = _binop("+", total, error)
    entry = metadata.get(fun.name, {})
    additions = {
        "csv_examples": entry.get("csv_examples", []) + [(row[:-1], row[-1]) for row in rows],
        "io_params": [name for name, _ in fun.args],
    }
    if all(ty in (st_int, st_float) for ty in columns):
        additions["training_data"] = entry.get("training_data", []) + rows
    metadata = metadata_update(metadata, fun, additions)
    return make_optimizer([total], fun, metadata, fitness_type, minimize=True, kind="csv")


def csv_data(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """Inline CSV: arguments followed by the expected result in each row.

    Columns follow the function's scalar types. Numeric outputs minimize
    squared error; Bool/String outputs minimize the number of mismatches.
    """
    assert len(decorator.macro_args) == 1, "csv_data decorator expects a single string argument"
    assert isinstance(decorator.macro_args[0], SLiteral) and isinstance(decorator.macro_args[0].value, str), (
        "csv_data decorator expects a string literal"
    )
    return _csv_specification(decorator.macro_args[0].value, fun, metadata)


def csv_file(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """File-backed version of ``csv_data``, with identical types and losses."""
    assert len(decorator.macro_args) == 1, "csv_file decorator expects a single string argument"
    assert isinstance(decorator.macro_args[0], SLiteral) and isinstance(decorator.macro_args[0].value, str), (
        "csv_file decorator expects a string literal"
    )
    with open(decorator.macro_args[0].value) as stream:
        return _csv_specification(stream.read(), fun, metadata)


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


def _scalar_literal(t: STerm):
    """The Python value of a scalar ``SLiteral`` (int, float, str, bool), or
    ``None`` if ``t`` is not such a literal. Bools are kept (unlike the numeric
    training-data extractor) since PBE specs may have Bool outputs."""
    if isinstance(t, SLiteral) and isinstance(t.value, (int, float, str, bool)):
        return t.value
    return None


def _is_list_nil(term: STerm) -> bool:
    """Whether ``term`` is ``nil`` / ``List.nil`` / ``List_nil`` (empty list)."""
    if isinstance(term, SQualifiedVar) and term.name.name == "nil":
        return True
    if isinstance(term, SVar):
        n = term.name.name
        return n == "nil" or n.endswith("_nil")
    return False


def _is_list_cons(term: STerm) -> bool:
    """Whether ``term`` is ``cons`` / ``List.cons`` / ``List_cons``."""
    if isinstance(term, SQualifiedVar) and term.name.name == "cons":
        return True
    if isinstance(term, SVar):
        n = term.name.name
        return n == "cons" or n.endswith("_cons")
    return False


def _list_literal_value(term: STerm) -> tuple | None:
    """Decode a sugar ``[e1, …, en]`` / ``List.cons`` nest into a Python tuple of
    scalar elements (Contata's ``List Int`` encoding), or ``None`` if the term is
    not a ground list literal."""
    if _is_list_nil(term):
        return ()
    if isinstance(term, SApplication) and isinstance(term.fun, SApplication) and _is_list_cons(term.fun.fun):
        head = _scalar_literal(term.fun.arg)
        tail = _list_literal_value(term.arg)
        if head is not None and tail is not None:
            return (head,) + tail
    return None


def _io_arg_value(t: STerm):
    """A ground ``@example`` argument: scalar literal or ``List Int`` literal."""
    v = _scalar_literal(t)
    if v is not None:
        return v
    return _list_literal_value(t)


def _io_call_target_matches(call_name: str, fun_name: Name) -> bool:
    """Whether a call head names the decorated function.

    Exact match wins. Under ``open Mod``, an assertion may be rebound to the
    module-prefixed library symbol (``List_length``) while the hole is still
    ``length`` — accept that *only* as a fallback, and prefer the local hole
    name when both could apply.
    """
    fname = fun_name.name
    if call_name == fname:
        return True
    # Prefixed library twin: ``List_length`` for hole ``length``.
    return call_name.endswith("_" + fname) and call_name != fname


def _io_call_args(term: STerm, fun_name: Name, decode=_io_arg_value):
    """If ``term`` is a fully-applied call ``fun_name(arg1)...(argN)`` with ground
    scalar or ``List Int`` literal arguments, return ``[v1, ..., vN]``
    (left-to-right); else ``None``.

    Under ``open List``, calls in ``@example`` assertions are often rebound to the
    module-prefixed canonical name (``List_length``) while the decorated hole is
    still ``length`` — accept that suffix match so Contata/PBE still see I/O.
    Prefer naming holes so they do not shadow library definitions (e.g. ``llen``
    instead of ``length`` when ``open List`` is in scope).
    """
    args: list = []
    current = term
    while isinstance(current, SApplication):
        v = decode(current.arg)
        if v is None:
            return None
        args.append(v)
        current = current.fun
    if not isinstance(current, SVar):
        return None
    if not _io_call_target_matches(current.name.name, fun_name):
        return None
    args.reverse()
    return args


def _extract_io_example(assertion: STerm, fun_name: Name, decode=_io_arg_value):
    """Extract a concrete I/O pair from an ``@example`` of the shape
    ``fun_name(arg1)...(argN) == out`` (in either order), where arguments and
    the output are scalar or ``List Int`` literals. Returns ``(inputs, output)``
    or ``None``. This is the structured PBE specification consumed by
    example-driven synthesizers (``afta``, ``contata``, …)."""
    if not (isinstance(assertion, SApplication) and isinstance(assertion.fun, SApplication)):
        return None
    op = assertion.fun.fun
    if not isinstance(op, SVar) or op.name.name != "==":
        return None
    lhs = assertion.fun.arg
    rhs = assertion.arg
    for call_side, out_side in ((lhs, rhs), (rhs, lhs)):
        out = decode(out_side)
        if out is None:
            continue
        args = _io_call_args(call_side, fun_name, decode)
        if args is not None:
            return (args, out)
    return None


def _constructor_literal_value(term: STerm, level: int = 0):
    """Decode closed scalar/registered-constructor syntax into runtime tuples."""
    from aeon.sugar.program import STypeApplication
    from aeon.verification.constructor_registry import get_constructor_fields

    if level > 16:
        return None
    if isinstance(term, SAnnotation):
        return _constructor_literal_value(term.expr, level)
    scalar = _scalar_literal(term)
    if scalar is not None:
        return scalar
    arguments: list = []
    while isinstance(term, (SApplication, STypeApplication)):
        if isinstance(term, STypeApplication):
            term = term.body
        else:
            argument = _constructor_literal_value(term.arg, level + 1)
            if argument is None:
                return None
            arguments.append(argument)
            term = term.fun
    if not isinstance(term, SVar):
        return None
    fields = get_constructor_fields(term.name.name)
    if fields is None or len(fields) != len(arguments):
        return None
    return (term.name.name, *reversed(arguments))


def _store_training_point(expr: STerm, fun: Definition, metadata: Metadata, *, maximize: bool = False) -> Metadata:
    """Extract labels only from a squared error (or its maximized negation).

    Minimizing f(x)-c does NOT ask for f(x)=c. Squared error has the known
    minimum zero at that label. The actual objective is always retained.
    """
    if maximize:
        if not (
            isinstance(expr, SApplication)
            and isinstance(expr.fun, SApplication)
            and isinstance(expr.fun.fun, SVar)
            and expr.fun.fun.name.name == "-"
            and isinstance(expr.fun.arg, SLiteral)
            and expr.fun.arg.value == 0
        ):
            return metadata
        expr = expr.arg
    if not (
        isinstance(expr, SApplication)
        and isinstance(expr.fun, SApplication)
        and isinstance(expr.fun.fun, SVar)
        and expr.fun.fun.name.name == "*"
        and expr.fun.arg == expr.arg
    ):
        return metadata
    point = _extract_training_point(expr.arg, fun.name)
    if point is not None:
        current_data = metadata.get(fun.name, {}).get("training_data", [])
        metadata = metadata_update(metadata, fun, {"training_data": current_data + [point]})
    return metadata


def minimize(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """Minimize a Float expression; recognized squared errors also provide labels."""
    assert len(decorator.macro_args) == 1, "minimize decorator expects a single argument"
    metadata = _store_training_point(decorator.macro_args[0], fun, metadata)
    return make_optimizer(decorator.macro_args, fun, metadata, st_float, minimize=True)


def maximize(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """Maximize a Float expression; negated squared errors also provide labels."""
    assert len(decorator.macro_args) == 1, "maximize decorator expects a single argument"
    metadata = _store_training_point(decorator.macro_args[0], fun, metadata, maximize=True)
    negated = _binop("-", SLiteral(0.0, st_float), decorator.macro_args[0])
    return make_optimizer([negated], fun, metadata, st_float, minimize=True)


def minimize_size(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """Minimize the total core AST size of this definition's hole replacements."""
    from aeon.errors import InvalidDecoratorArgumentError

    if decorator.macro_args:
        raise InvalidDecoratorArgumentError(decorator, "expected no arguments; use @minimize_size")
    goals = metadata.get(fun.name, {}).get("goals", [])
    goal = Goal(minimize=True, length=1, function=fun.name, kind="size")
    return fun, [], metadata_update(metadata, fun, {"goals": goals + [goal]})


def minimize_cputime(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """Adds CPU time of the given expression as a synthesis objective.

    Usage: ``@minimize_cputime(func 42)``.

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

    Usage: @minimize_energy(func 42)

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
