"""Aeon adapter for bounded structure-guided list/tree-to-list synthesis.

Adapted from Lin and Morihata's size-recurrence and structure/element
separation approaches (JSSST 2025, GPCE 2026). This implements the constructor
word / integer element subset, not the full published language or evaluation.
"""

from __future__ import annotations

from dataclasses import dataclass
import time

from aeon.core.instantiation import type_substitution
from aeon.core.substitutions import instantiate_refinement_in_type
from aeon.core.terms import Abstraction, Application, Literal, Rec, RefinementApplication, Term, TypeApplication, Var
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    RefinementPolymorphism,
    Type,
    TypeConstructor,
    TypePolymorphism,
    t_bool,
    t_int,
)
from aeon.synthesis.api import Synthesizer, SynthesisNotSuccessful, UnsupportedSynthesisGoal
from aeon.synthesis.modules.structure_guided.search import Config, Example, Expr, Node, Search, Solution, Stats
from aeon.synthesis.modules.sygus.solver import _apply_op, _num_literal
from aeon.synthesis.modules.symetric.synthesizer import base_key
from aeon.synthesis.uis.api import SynthesisUI
from aeon.utils.name import Name, fresh_counter
from aeon.verification.constructor_registry import get_constructor_order


def fresh(label: str) -> Name:
    identifier = fresh_counter.fresh()
    return Name(f"_structure_{label}_{identifier}", identifier)


def bare(ty: Type) -> Type:
    return ty.type if isinstance(ty, RefinedType) else ty


def apply(head: Term, *arguments: Term) -> Term:
    for argument in arguments:
        head = Application(head, argument)
    return head


def instantiate(ctx, label: str, arguments: list[Type]) -> tuple[Term, Type]:
    match_ = next(((name, ty) for name, ty in ctx.concrete_vars() if name.name == label), None)
    if match_ is None:
        raise UnsupportedSynthesisGoal(f"structure_guided: generated datatype function {label} is not in scope")
    name, ty = match_
    head: Term = Var(name)
    remaining = iter(arguments)
    while isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
        if isinstance(ty, TypePolymorphism):
            argument = next(remaining, None)
            if argument is None:
                raise UnsupportedSynthesisGoal("structure_guided: unsupported datatype polymorphism")
            head = TypeApplication(head, argument)
            ty = type_substitution(ty.body, ty.name, argument)
        else:
            sort = ty.sort
            parameters = []
            while isinstance(sort, AbstractionType):
                parameters.append(fresh("predicate"))
                sort = sort.type
            predicate: Term = Literal(True, t_bool)
            for parameter in reversed(parameters):
                predicate = Abstraction(parameter, predicate)
            if not isinstance(predicate, Abstraction):
                raise UnsupportedSynthesisGoal("structure_guided: unsupported abstract-refinement sort")
            head = RefinementApplication(head, predicate)
            ty = instantiate_refinement_in_type(ty.body, ty.name, predicate)
    if next(remaining, None) is not None:
        raise UnsupportedSynthesisGoal("structure_guided: datatype type-argument mismatch")
    return head, ty


@dataclass(frozen=True)
class Schema:
    type: TypeConstructor
    tags: tuple[str, ...]
    empty: str
    node: str
    fields: tuple[str, ...]  # "int" or "self", in constructor declaration order
    empty_head: Term
    node_head: Term

    @property
    def arity(self):
        return self.fields.count("self")


def schema(ctx, ty: Type) -> Schema:
    ty = bare(ty)
    if not isinstance(ty, TypeConstructor):
        raise UnsupportedSynthesisGoal("structure_guided: inputs and results must be registered recursive ADTs")
    order = get_constructor_order(ty.name.name)
    if order is None:
        raise UnsupportedSynthesisGoal("structure_guided: inputs and results must be registered recursive ADTs")
    if len(order) != 2:
        raise UnsupportedSynthesisGoal("structure_guided: ADTs need an empty constructor and one recursive constructor")
    empty = node = None
    for tag in order:
        head, signature = instantiate(ctx, tag, ty.args)
        fields = []
        while isinstance(signature, AbstractionType):
            key = base_key(bare(signature.var_type))
            if key == base_key(t_int):
                fields.append("int")
            elif key == base_key(ty):
                fields.append("self")
            else:
                raise UnsupportedSynthesisGoal("structure_guided: constructor fields must be Int or the input datatype")
            signature = signature.type
        if base_key(bare(signature)) != base_key(ty):
            raise UnsupportedSynthesisGoal("structure_guided: constructor result has an unsupported type")
        if not fields:
            empty = tag, head
        elif 1 <= fields.count("self") <= 2 and 1 <= fields.count("int") <= 2:
            node = tag, head, tuple(fields)
    if empty is None or node is None:
        raise UnsupportedSynthesisGoal(
            "structure_guided: needs a nullary base and an Int-labelled list/binary-tree node"
        )
    return Schema(ty, tuple(order), empty[0], node[0], node[2], empty[1], node[1])


def decode(value, shape: Schema, config: Config) -> Node | None:
    remaining = config.max_nodes

    def visit(current, depth):
        nonlocal remaining
        remaining -= 1
        if remaining < 0 or depth > config.max_depth:
            raise UnsupportedSynthesisGoal("structure_guided: example exceeds datatype bounds")
        if type(current) is not tuple or not current:
            raise UnsupportedSynthesisGoal("structure_guided: examples must use registered constructor literals")
        if current[0] == shape.empty and len(current) == 1:
            return None
        if current[0] != shape.node or len(current) != len(shape.fields) + 1:
            raise UnsupportedSynthesisGoal("structure_guided: example constructor does not match its datatype")
        scalars, children = [], []
        for kind, field in zip(shape.fields, current[1:]):
            if kind == "int":
                if type(field) is not int:
                    raise UnsupportedSynthesisGoal("structure_guided: expected an Int constructor field")
                scalars.append(field)
            else:
                children.append(visit(field, depth + 1))
        return Node(tuple(scalars), tuple(children))

    return visit(value, 0)


def flatten(node: Node | None) -> tuple[int, ...]:
    output = []
    while node is not None:
        output.append(node.values[0])
        node = node.children[0]
    return tuple(output)


def recursor(ctx, shape: Schema, result: Type, scrutinee: Term, base: Term, step: Term) -> Term:
    head, _ = instantiate(ctx, shape.type.name.name + "_rec", [*shape.type.args, result])
    handlers = {shape.empty: base, shape.node: step}
    return apply(head, scrutinee, *(handlers[tag] for tag in shape.tags))


def construct(shape: Schema, element: Term, tail: Term) -> Term:
    return apply(shape.node_head, *(element if kind == "int" else tail for kind in shape.fields))


def expression(expr: Expr, variables: list[Name]) -> Term:
    if expr.op == "var":
        return Var(variables[expr.value])
    if expr.op == "const":
        return _num_literal(expr.value, t_int)
    return _apply_op(expr.op, t_int, *(expression(a, variables) for a in expr.args))


def core_candidate(ctx, input_shape: Schema, output_shape: Schema, function: Name, parameter: Name, solution: Solution):
    """Build real core constructors, immediate-child self-calls and an optional append helper."""
    fields = [fresh("field") for _ in input_shape.fields]
    scalars = [name for kind, name in zip(input_shape.fields, fields) if kind == "int"]
    children = [name for kind, name in zip(input_shape.fields, fields) if kind == "self"]
    append_name = fresh("append")
    tail = output_shape.empty_head
    needs_append = False
    for i in reversed(range(len(solution.word))):
        token = solution.word[i]
        if token == -1:
            tail = construct(output_shape, expression(solution.elements[(1, i)], scalars), tail)
        else:
            call = apply(Var(function), Var(children[token]))
            if i == len(solution.word) - 1:
                tail = call
            else:
                needs_append = True
                tail = apply(Var(append_name), call, tail)
    for field in reversed(fields):
        tail = Abstraction(field, tail)
    base = output_shape.empty_head
    for i in reversed(range(solution.base)):
        base = construct(output_shape, expression(solution.elements[(0, i)], []), base)
    body = recursor(ctx, input_shape, output_shape.type, Var(parameter), base, tail)
    if needs_append:
        # A local, verified append is generated from the output constructors.
        # No user function is silently assumed to have concatenation semantics.
        xs, ys, hd, tl = (fresh(label) for label in ("xs", "ys", "head", "tail"))
        node_fields = [hd if kind == "int" else tl for kind in output_shape.fields]
        step: Term = construct(output_shape, Var(hd), apply(Var(append_name), Var(tl), Var(ys)))
        for name in reversed(node_fields):
            step = Abstraction(name, step)
        append_body = recursor(ctx, output_shape, output_shape.type, Var(xs), Var(ys), step)
        signature = AbstractionType(xs, output_shape.type, AbstractionType(ys, output_shape.type, output_shape.type))
        body = Rec(append_name, signature, Abstraction(xs, Abstraction(ys, append_body)), body)
    return body


class StructureGuidedSynthesizer(Synthesizer):
    def __init__(self, config: Config | None = None):
        self.config = config or Config.from_env()
        self.stats = Stats()

    def computations(self, primitives):
        return {}

    def synthesize(
        self, ctx, type, validate, evaluate, fun_name, metadata, budget=60, ui=SynthesisUI(), output_value=None
    ):
        started = time.monotonic()
        self.stats = Stats()
        entry = metadata.get(fun_name, {})
        rows = entry.get("constructor_io_examples", [])
        parameters = entry.get("io_params", [])
        if not rows or len(parameters) != 1 or not callable(entry.get("pbe_probe")):
            raise UnsupportedSynthesisGoal("structure_guided: needs unary constructor-literal @example I/O pairs")
        if not entry.get("recursion"):
            raise UnsupportedSynthesisGoal("structure_guided: recursive search requires @allow_recursion")
        if len(entry.get("goals", [])) > len(entry.get("examples", [])) or len(rows) != len(entry.get("examples", [])):
            raise UnsupportedSynthesisGoal(
                "structure_guided: supports I/O examples, not additional objectives or relational goals"
            )
        parameter = parameters[0]
        input_type = ctx.type_of(parameter)
        signature = ctx.type_of(fun_name)
        if input_type is None or signature is None:
            raise UnsupportedSynthesisGoal("structure_guided: function and parameter must be in scope")
        input_shape, output_shape = schema(ctx, input_type), schema(ctx, type)
        if output_shape.arity != 1 or output_shape.fields.count("int") != 1:
            raise UnsupportedSynthesisGoal("structure_guided: output must be an Int-labelled list datatype")
        examples = []
        for arguments, output in rows:
            if len(arguments) != 1:
                raise UnsupportedSynthesisGoal("structure_guided: example arity must be one")
            examples.append(
                Example(
                    decode(arguments[0], input_shape, self.config), flatten(decode(output, output_shape, self.config))
                )
            )
        search = Search(tuple(examples), input_shape.arity, self.config, budget - (time.monotonic() - started))
        self.stats = search.stats
        for solution in search.solutions():
            search.tick()
            candidate = core_candidate(ctx, input_shape, output_shape, fun_name, parameter, solution)
            if not validate(candidate):
                self.stats.validation_rejections += 1
                continue
            # Tie the recursive knot to THIS candidate, rather than the dummy
            # implementation in the per-hole probe's prefix environment.
            tied = Rec(fun_name, signature, Abstraction(parameter, candidate), apply(Var(fun_name), Var(parameter)))
            try:
                consistent = True
                for arguments, expected in rows:
                    search.tick()
                    if entry["pbe_probe"](tied, list(arguments)) != expected:
                        consistent = False
                        break
            except (TypeError, ValueError, KeyError, RecursionError):
                consistent = False
            if not consistent:
                self.stats.runtime_rejections += 1
                continue
            ui.register(candidate, [0.0] * len(rows), time.monotonic() - started, True)
            return candidate
        raise SynthesisNotSuccessful("structure_guided: no validated program within the configured grammar")
