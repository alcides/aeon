import argparse
import os
import time
import csv
from typing import Any
from abc import ABC, abstractmethod
from dataclasses import dataclass
from geneticengine.grammar import extract_grammar
from geneticengine.prelude import abstract
from typing import Tuple, Callable
from geneticengine.grammar.decorators import weight
from geneticengine.problems import SingleObjectiveProblem
from geneticengine.algorithms.gp.operators.combinators import ParallelStep, SequenceStep
from geneticengine.algorithms.gp.operators.crossover import GenericCrossoverStep
from geneticengine.algorithms.gp.operators.mutation import GenericMutationStep
from geneticengine.algorithms.gp.operators.selection import TournamentSelection
from geneticengine.algorithms.gp.operators.elitism import ElitismStep
from geneticengine.algorithms.gp.operators.novelty import NoveltyStep
from geneticengine.prelude import GeneticProgramming
from geneticengine.random.sources import NativeRandomSource
from geneticengine.evaluation.budget import TimeBudget
from geneticengine.representations.tree.treebased import TreeBasedRepresentation
from geneticengine.representations.tree.initializations import MaxDepthDecider
from geneticengine.grammar.grammar import extract_grammar
from aeon.bindings.arc_dsl import *
from aeon.bindings.arc_constants import *
from aeon.bindings.task_dsl import load_arc_task_by_id, evaluate_on_train_impl, evaluate_on_test_impl

# ======================================================================================
# Abstract Base Classes for the Genetic Programming Grammar
# ======================================================================================


class Expression(ABC):
    """Base class for all expressions in the DSL."""

    @abstractmethod
    def evaluate(self, *args, **kwargs) -> Any:
        pass

    def __str__(self) -> str:
        args = ", ".join([str(v) for v in self.__dict__.values()])
        return f"{self.__class__.__name__}({args})"


@abstract
class NumericalExpression(Expression):
    def evaluate(self, *args, **kwargs) -> Numerical: ...


@abstract
class BooleanExpression(Expression):
    def evaluate(self, *args, **kwargs) -> Boolean: ...


@abstract
class GridExpression(Expression):
    def evaluate(self, *args, **kwargs) -> Grid: ...


@abstract
class ObjectExpression(Expression):
    def evaluate(self, *args, **kwargs) -> Object: ...


@abstract
class ObjectsExpression(Expression):
    def evaluate(self, *args, **kwargs) -> Objects: ...


@abstract
class IndicesExpression(Expression):
    def evaluate(self, *args, **kwargs) -> Indices: ...


@abstract
class IntegerExpression(NumericalExpression):
    def evaluate(self, *args, **kwargs) -> Integer: ...


@abstract
class ContainerExpression(Expression):
    """An expression that evaluates to a Container (e.g., Tuple, FrozenSet)."""

    def evaluate(self, *args, **kwargs) -> Container: ...


@abstract
class TupleExpression(ContainerExpression):
    """An expression that evaluates to a Tuple."""

    def evaluate(self, *args, **kwargs) -> Tuple: ...


@abstract
class FrozenSetExpression(ContainerExpression):
    """An expression that evaluates to a FrozenSet."""

    def evaluate(self, *args, **kwargs) -> FrozenSet: ...


@abstract
class CallableExpression(Expression):
    """An expression that evaluates to a callable function."""

    def evaluate(self, *args, **kwargs) -> Callable: ...


@abstract
class PatchExpression(Expression):
    """An expression that evaluates to a Patch (Object or Indices)."""

    def evaluate(self, *args, **kwargs) -> Patch: ...


@abstract
class ElementExpression(Expression):
    """An expression that evaluates to an Element (Object or Grid)."""

    def evaluate(self, *args, **kwargs) -> Element: ...


@abstract
class PieceExpression(Expression):
    """An expression that evaluates to a Piece (Grid or Patch)."""

    def evaluate(self, *args, **kwargs) -> Piece: ...


# ======================================================================================
# Terminal Expressions
# ======================================================================================


@dataclass
class Constant(IntegerExpression):
    value: Integer

    def evaluate(self, *args, **kwargs) -> Integer:
        return self.value

    def __str__(self) -> str:
        return str(self.value)


@dataclass
@weight(970)
class InputGrid(GridExpression):
    """A typed input node specifically for the ARC task grid."""

    def evaluate(self, *args, **kwargs) -> Grid:
        return kwargs.get("input_grid", tuple())

    def __str__(self) -> str:
        return "input_grid"


# ======================================================================================
# DSL Functions as Classes
# ======================================================================================


@dataclass
@weight(72)
class Identity(Expression):
    x: Expression

    def evaluate(self, *args, **kwargs) -> Any:
        return identity(self.x.evaluate(**kwargs))


@dataclass
@weight(51)
class AddInteger(IntegerExpression):
    left: IntegerExpression
    right: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return add(self.left.evaluate(**kwargs), self.right.evaluate(**kwargs))
    
@dataclass
@weight(51)
class AddTuple(TupleExpression):
    left: TupleExpression
    right: TupleExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return add(self.left.evaluate(**kwargs), self.right.evaluate(**kwargs))


@dataclass
@weight(59)
class SubtractInteger(IntegerExpression):
    left: IntegerExpression
    right: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return subtract(self.left.evaluate(**kwargs), self.right.evaluate(**kwargs))

@dataclass
@weight(59)
class SubtractTuple(TupleExpression):
    left: TupleExpression
    right: TupleExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return subtract(self.left.evaluate(**kwargs), self.right.evaluate(**kwargs))


@dataclass
@weight(49)
class MultiplyInteger(IntegerExpression):
    left: IntegerExpression
    right: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return multiply(self.left.evaluate(**kwargs), self.right.evaluate(**kwargs))

@dataclass
@weight(49)
class MultiplyTuple(TupleExpression):
    left: TupleExpression
    right: TupleExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return multiply(self.left.evaluate(**kwargs), self.right.evaluate(**kwargs))


@dataclass
@weight(7)
class DivideInteger(IntegerExpression):
    left: IntegerExpression
    right: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return divide(self.left.evaluate(**kwargs), self.right.evaluate(**kwargs))

@dataclass
@weight(7)
class DivideTuple(TupleExpression):
    left: TupleExpression
    right: TupleExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return divide(self.left.evaluate(**kwargs), self.right.evaluate(**kwargs))


@dataclass
@weight(20)
class InvertInteger(IntegerExpression):
    n: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return invert(self.n.evaluate(**kwargs))

@dataclass
@weight(20)
class InvertTuple(TupleExpression):
    n: TupleExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return invert(self.n.evaluate(**kwargs))


@dataclass
@weight(26)
class Even(BooleanExpression):
    n: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Boolean:
        return even(self.n.evaluate(**kwargs))


@dataclass
@weight(18)
class DoubleInteger(IntegerExpression):
    n: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return double(self.n.evaluate(**kwargs))

@dataclass
@weight(18)
class DoubleTuple(TupleExpression):
    n: TupleExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return double(self.n.evaluate(**kwargs))


@dataclass
@weight(9)
class HalveInteger(IntegerExpression):
    n: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return halve(self.n.evaluate(**kwargs))


@dataclass
@weight(9)
class HalveTuple(TupleExpression):
    n: TupleExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return halve(self.n.evaluate(**kwargs))


@weight(25)
@dataclass
class Flip(BooleanExpression):
    b: BooleanExpression

    def evaluate(self, *args, **kwargs) -> Boolean:
        return flip(self.b.evaluate(**kwargs))


@dataclass
@weight(44)
class Equality(BooleanExpression):
    left: Expression
    right: Expression

    def evaluate(self, *args, **kwargs) -> Boolean:
        return equality(self.left.evaluate(**kwargs), self.right.evaluate(**kwargs))


@dataclass
@weight(26)
class Contained(BooleanExpression):
    """Checks if a value is in a container."""

    value: Expression
    container: ContainerExpression

    def evaluate(self, *args, **kwargs) -> Boolean:
        return contained(self.value.evaluate(**kwargs), self.container.evaluate(**kwargs))


@dataclass
@weight(60)
class Combine(ContainerExpression):
    """Combines two containers."""

    a: ContainerExpression
    b: ContainerExpression

    def evaluate(self, *args, **kwargs) -> Container:
        return combine(self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(35)
class Intersection(FrozenSetExpression):
    """Calculates the intersection of two frozensets."""

    a: FrozenSetExpression
    b: FrozenSetExpression

    def evaluate(self, *args, **kwargs) -> FrozenSet:
        return intersection(self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(59)
class Difference(FrozenSetExpression):
    """Calculates the difference between two frozensets."""

    a: FrozenSetExpression
    b: FrozenSetExpression

    def evaluate(self, *args, **kwargs) -> FrozenSet:
        return difference(self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(8)
class Dedupe(TupleExpression):
    """Removes duplicates from a tuple."""

    tup: TupleExpression

    def evaluate(self, *args, **kwargs) -> Tuple:
        return dedupe(self.tup.evaluate(**kwargs))


@dataclass
@weight(37)
class Order(TupleExpression):
    """Orders a container using a key function."""

    container: ContainerExpression
    compfunc: CallableExpression

    def evaluate(self, *args, **kwargs) -> Tuple:
        return order(self.container.evaluate(**kwargs), self.compfunc.evaluate(**kwargs))


@dataclass
@weight(9)
class Repeat(TupleExpression):
    """Repeats an item N times to create a tuple."""

    item: Expression
    num: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Tuple:
        return repeat(self.item.evaluate(**kwargs), self.num.evaluate(**kwargs))


@dataclass
@weight(31)
class Greater(BooleanExpression):
    """Checks if a > b."""

    a: IntegerExpression
    b: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Boolean:
        return greater(self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(141)
class Size(IntegerExpression):
    """Returns the size (length) of a container."""

    container: ContainerExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return size(self.container.evaluate(**kwargs))


@dataclass
@weight(78)
class Merge(ContainerExpression):
    """Merges a container of containers into a single container."""

    containers: ContainerExpression

    def evaluate(self, *args, **kwargs) -> Container:
        return merge(self.containers.evaluate(**kwargs))


@dataclass
@weight(11)
class Maximum(IntegerExpression):
    """Finds the maximum value in a set of integers."""

    container: FrozenSetExpression  # Specifically IntegerSet

    def evaluate(self, *args, **kwargs) -> Integer:
        return maximum(self.container.evaluate(**kwargs))


@dataclass
@weight(6)
class Minimum(IntegerExpression):
    """Finds the minimum value in a set of integers."""

    container: FrozenSetExpression  # Specifically IntegerSet

    def evaluate(self, *args, **kwargs) -> Integer:
        return minimum(self.container.evaluate(**kwargs))


@dataclass
@weight(8)
class Valmax(IntegerExpression):
    """Finds the maximum value of a container according to a key function."""

    container: ContainerExpression
    compfunc: CallableExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return valmax(self.container.evaluate(**kwargs), self.compfunc.evaluate(**kwargs))


@dataclass
@weight(4)
class Valmin(IntegerExpression):
    """Finds the minimum value of a container according to a key function."""

    container: ContainerExpression
    compfunc: CallableExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return valmin(self.container.evaluate(**kwargs), self.compfunc.evaluate(**kwargs))


@dataclass
@weight(64)
class Argmax(Expression):
    """Finds the item in a container that maximizes a key function."""

    container: ContainerExpression
    compfunc: CallableExpression

    def evaluate(self, *args, **kwargs) -> Any:
        return argmax(self.container.evaluate(**kwargs), self.compfunc.evaluate(**kwargs))


@dataclass
@weight(32)
class Argmin(Expression):
    """Finds the item in a container that minimizes a key function."""

    container: ContainerExpression
    compfunc: CallableExpression

    def evaluate(self, *args, **kwargs) -> Any:
        return argmin(self.container.evaluate(**kwargs), self.compfunc.evaluate(**kwargs))


@dataclass
@weight(4)
class MostCommon(Expression):
    """Finds the most common item in a container."""

    container: ContainerExpression

    def evaluate(self, *args, **kwargs) -> Any:
        return mostcommon(self.container.evaluate(**kwargs))


@dataclass
@weight(3)
class LeastCommon(Expression):
    """Finds the least common item in a container."""

    container: ContainerExpression

    def evaluate(self, *args, **kwargs) -> Any:
        return leastcommon(self.container.evaluate(**kwargs))


@dataclass
@weight(44)
class Initset(FrozenSetExpression):
    """Initializes a frozenset with a single value."""

    value: Expression

    def evaluate(self, *args, **kwargs) -> FrozenSet:
        return initset(self.value.evaluate(**kwargs))


@dataclass
@weight(9)
class Both(BooleanExpression):
    """Logical AND for two boolean expressions."""

    a: BooleanExpression
    b: BooleanExpression

    def evaluate(self, *args, **kwargs) -> Boolean:
        return both(self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(13)
class Either(BooleanExpression):
    """Logical OR for two boolean expressions."""

    a: BooleanExpression
    b: BooleanExpression

    def evaluate(self, *args, **kwargs) -> Boolean:
        return either(self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(18)
class IncrementInteger(IntegerExpression):
    """Increments an integer value by 1."""

    x: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return increment(self.x.evaluate(**kwargs))
    
@dataclass
@weight(18)
class IncrementTuple(TupleExpression):
    x: TupleExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return increment(self.x.evaluate(**kwargs))


@dataclass
@weight(39)
class DecrementInteger(IntegerExpression):
    """Decrements an integer value by 1."""

    x: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return decrement(self.x.evaluate(**kwargs))

@dataclass
@weight(39)
class DecrementTuple(TupleExpression):
    x: TupleExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return decrement(self.x.evaluate(**kwargs))
    
@dataclass
@weight(63)
class CrementInteger(IntegerExpression):
    """Increments positive values, decrements negative values."""

    x: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return crement(self.x.evaluate(**kwargs))
    
@dataclass
@weight(63)
class CrementTuple(TupleExpression):
    x: TupleExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return crement(self.x.evaluate(**kwargs))


@dataclass
@weight(3)
class SignInteger(IntegerExpression):
    """Returns the sign of an integer value."""

    x: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return sign(self.x.evaluate(**kwargs))

@dataclass
@weight(9)
class SignTuple(TupleExpression):
    x: TupleExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return sign(self.x.evaluate(**kwargs))

@dataclass
@weight(9)
class Positive(BooleanExpression):
    """Checks if an integer is positive."""

    x: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Boolean:
        return positive(self.x.evaluate(**kwargs))


@dataclass
@weight(20)
class Toivec(TupleExpression):
    """Creates a vertical vector (i, 0)."""

    i: IntegerExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return toivec(self.i.evaluate(**kwargs))


@dataclass
@weight(24)
class Tojvec(TupleExpression):
    """Creates a horizontal vector (0, j)."""

    j: IntegerExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return tojvec(self.j.evaluate(**kwargs))


@dataclass
@weight(101)
class Sfilter(ContainerExpression):
    """Filters a container based on a condition."""

    container: ContainerExpression
    condition: CallableExpression

    def evaluate(self, *args, **kwargs) -> Container:
        return sfilter(self.container.evaluate(**kwargs), self.condition.evaluate(**kwargs))


@dataclass
@weight(40)
class Mfilter(FrozenSetExpression):
    """Filters a container of containers and merges the result."""

    container: ContainerExpression
    function: CallableExpression

    def evaluate(self, *args, **kwargs) -> FrozenSet:
        return mfilter(self.container.evaluate(**kwargs), self.function.evaluate(**kwargs))


@dataclass
@weight(31)
class Extract(Expression):
    """Extracts the first element that satisfies a condition."""

    container: ContainerExpression
    condition: CallableExpression

    def evaluate(self, *args, **kwargs) -> Any:
        return extract(self.container.evaluate(**kwargs), self.condition.evaluate(**kwargs))


@dataclass
@weight(11)
class Totuple(TupleExpression):
    """Converts a frozenset to a tuple."""

    container: FrozenSetExpression

    def evaluate(self, *args, **kwargs) -> Tuple:
        return totuple(self.container.evaluate(**kwargs))


@dataclass
@weight(168)
class First(Expression):
    """Gets the first item of a container."""

    container: ContainerExpression

    def evaluate(self, *args, **kwargs) -> Any:
        return first(self.container.evaluate(**kwargs))


@dataclass
@weight(82)
class Last(Expression):
    """Gets the last item of a container."""

    container: ContainerExpression

    def evaluate(self, *args, **kwargs) -> Any:
        return last(self.container.evaluate(**kwargs))


@dataclass
@weight(35)
class Insert(FrozenSetExpression):
    """Inserts an item into a frozenset."""

    value: Expression
    container: FrozenSetExpression

    def evaluate(self, *args, **kwargs) -> FrozenSet:
        return insert(self.value.evaluate(**kwargs), self.container.evaluate(**kwargs))


@dataclass
@weight(35)
class Remove(ContainerExpression):
    """Removes an item from a container."""

    value: Expression
    container: ContainerExpression

    def evaluate(self, *args, **kwargs) -> Container:
        return remove(self.value.evaluate(**kwargs), self.container.evaluate(**kwargs))


@dataclass
@weight(17)
class Other(Expression):
    """Gets the other value in a two-element container."""

    container: ContainerExpression
    value: Expression

    def evaluate(self, *args, **kwargs) -> Any:
        return other(self.container.evaluate(**kwargs), self.value.evaluate(**kwargs))


@dataclass
@weight(40)
class Interval(TupleExpression):
    """Creates a tuple representing a range."""

    start: IntegerExpression
    stop: IntegerExpression
    step: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Tuple:
        return interval(self.start.evaluate(**kwargs), self.stop.evaluate(**kwargs), self.step.evaluate(**kwargs))


@dataclass
@weight(128)
class Astuple(TupleExpression):
    """Constructs a tuple from two integers."""

    a: IntegerExpression
    b: IntegerExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return astuple(self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(20)
class Product(FrozenSetExpression):
    """Creates the Cartesian product of two containers."""

    a: ContainerExpression
    b: ContainerExpression

    def evaluate(self, *args, **kwargs) -> FrozenSet:
        return product(self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(23)
class Pair(TupleExpression):
    """Zips two tuples together."""

    a: TupleExpression
    b: TupleExpression

    def evaluate(self, *args, **kwargs) -> TupleTuple:
        return pair(self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(80)
class Branch(Expression):
    """If-else branching."""

    condition: BooleanExpression
    a: Expression
    b: Expression

    def evaluate(self, *args, **kwargs) -> Any:
        return branch(self.condition.evaluate(**kwargs), self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(293)
class Compose(CallableExpression):
    """Function composition: outer(inner(x))."""

    outer: CallableExpression
    inner: CallableExpression

    def evaluate(self, *args, **kwargs) -> Callable:
        return compose(self.outer.evaluate(**kwargs), self.inner.evaluate(**kwargs))


@dataclass
@weight(129)
class Chain(CallableExpression):
    """Three-function composition: h(g(f(x)))."""

    h: CallableExpression
    g: CallableExpression
    f: CallableExpression

    def evaluate(self, *args, **kwargs) -> Callable:
        return chain(self.h.evaluate(**kwargs), self.g.evaluate(**kwargs), self.f.evaluate(**kwargs))


@dataclass
@weight(55)
class Matcher(CallableExpression):
    """Creates an equality checking function: lambda x: function(x) == target."""

    function: CallableExpression
    target: Expression

    def evaluate(self, *args, **kwargs) -> Callable:
        return matcher(self.function.evaluate(**kwargs), self.target.evaluate(**kwargs))


@dataclass
@weight(231)
class Rbind(CallableExpression):
    """Fixes the rightmost argument of a function."""

    function: CallableExpression
    fixed: Expression

    def evaluate(self, *args, **kwargs) -> Callable:
        return rbind(self.function.evaluate(**kwargs), self.fixed.evaluate(**kwargs))


@dataclass
@weight(263)
class Lbind(CallableExpression):
    """Fixes the leftmost argument of a function."""

    function: CallableExpression
    fixed: Expression

    def evaluate(self, *args, **kwargs) -> Callable:
        return lbind(self.function.evaluate(**kwargs), self.fixed.evaluate(**kwargs))


@dataclass
@weight(21)
class Power(CallableExpression):
    """Applies a function N times."""

    function: CallableExpression
    n: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Callable:
        return power(self.function.evaluate(**kwargs), self.n.evaluate(**kwargs))


@dataclass
@weight(279)
class Fork(CallableExpression):
    """Creates a wrapper: lambda x: outer(a(x), b(x))."""

    outer: CallableExpression
    a: CallableExpression
    b: CallableExpression

    def evaluate(self, *args, **kwargs) -> Callable:
        return fork(self.outer.evaluate(**kwargs), self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(447)
class Apply(ContainerExpression):
    """Applies a function to each item in a container."""

    function: CallableExpression
    container: ContainerExpression

    def evaluate(self, *args, **kwargs) -> Container:
        return apply(self.function.evaluate(**kwargs), self.container.evaluate(**kwargs))


@dataclass
@weight(19)
class Rapply(ContainerExpression):
    """Applies each function in a container to a single value."""

    functions: ContainerExpression
    value: Expression

    def evaluate(self, *args, **kwargs) -> Container:
        return rapply(self.functions.evaluate(**kwargs), self.value.evaluate(**kwargs))


@dataclass
@weight(208)
class Mapply(FrozenSetExpression):
    """Applies a function to a container of containers and merges the result."""

    function: CallableExpression
    container: ContainerExpression

    def evaluate(self, *args, **kwargs) -> FrozenSet:
        return mapply(self.function.evaluate(**kwargs), self.container.evaluate(**kwargs))


@dataclass
@weight(27)
class Papply(TupleExpression):
    """Applies a function element-wise to two tuples."""

    function: CallableExpression
    a: TupleExpression
    b: TupleExpression

    def evaluate(self, *args, **kwargs) -> Tuple:
        return papply(self.function.evaluate(**kwargs), self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(208)
class Mpapply(TupleExpression):
    """Applies a function element-wise to two tuples and merges the results."""

    function: CallableExpression
    a: TupleExpression
    b: TupleExpression

    def evaluate(self, *args, **kwargs) -> Tuple:
        return mpapply(self.function.evaluate(**kwargs), self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(12)
class Prapply(FrozenSetExpression):
    """Applies a function to the Cartesian product of two containers."""

    function: CallableExpression
    a: ContainerExpression
    b: ContainerExpression

    def evaluate(self, *args, **kwargs) -> FrozenSet:
        return prapply(self.function.evaluate(**kwargs), self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(23)
class Mostcolor(IntegerExpression):
    """Finds the most common color in an Element."""

    element: ElementExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return mostcolor(self.element.evaluate(**kwargs))


@dataclass
@weight(45)
class Leastcolor(IntegerExpression):
    """Finds the least common color in an Element."""

    element: ElementExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return leastcolor(self.element.evaluate(**kwargs))


@dataclass
@weight(43)
class Height(IntegerExpression):
    """Calculates the height of a Piece."""

    piece: PieceExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return height(self.piece.evaluate(**kwargs))


@dataclass
@weight(50)
class Width(IntegerExpression):
    """Calculates the width of a Piece."""

    piece: PieceExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return width(self.piece.evaluate(**kwargs))


@dataclass
@weight(30)
class Shape(TupleExpression):
    """Gets the (height, width) of a Piece."""

    piece: PieceExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return shape(self.piece.evaluate(**kwargs))


@dataclass
@weight(12)
class Portrait(BooleanExpression):
    """Checks if a Piece is taller than it is wide."""

    piece: PieceExpression

    def evaluate(self, *args, **kwargs) -> Boolean:
        return portrait(self.piece.evaluate(**kwargs))


@dataclass
@weight(22)
class Colorcount(IntegerExpression):
    """Counts cells of a specific color in an Element."""

    element: ElementExpression
    value: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return colorcount(self.element.evaluate(**kwargs), self.value.evaluate(**kwargs))


@dataclass
@weight(63)
class Colorfilter(ObjectsExpression):
    """Filters objects by color."""

    objs: ObjectsExpression
    value: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Objects:
        return colorfilter(self.objs.evaluate(**kwargs), self.value.evaluate(**kwargs))


@dataclass
@weight(29)
class Sizefilter(FrozenSetExpression):
    """Filters items in a container by their size."""

    container: ContainerExpression
    n: IntegerExpression

    def evaluate(self, *args, **kwargs) -> FrozenSet:
        return sizefilter(self.container.evaluate(**kwargs), self.n.evaluate(**kwargs))


@dataclass
@weight(21)
class Asindices(IndicesExpression):
    """Gets the indices of all cells in a grid."""

    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Indices:
        return asindices(self.grid.evaluate(**kwargs))


@dataclass
@weight(183)
class Ofcolor(IndicesExpression):
    """Gets indices of cells with a specific color in a grid."""

    grid: GridExpression
    value: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Indices:
        return ofcolor(self.grid.evaluate(**kwargs), self.value.evaluate(**kwargs))


@dataclass
@weight(58)
class Ulcorner(TupleExpression):
    """Gets the upper-left corner index of a Patch."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return ulcorner(self.patch.evaluate(**kwargs))


@dataclass
@weight(16)
class Urcorner(TupleExpression):
    """Gets the upper-right corner index of a Patch."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return urcorner(self.patch.evaluate(**kwargs))


@dataclass
@weight(9)
class Llcorner(TupleExpression):
    """Gets the lower-left corner index of a Patch."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return llcorner(self.patch.evaluate(**kwargs))


@dataclass
@weight(15)
class Lrcorner(TupleExpression):
    """Gets the lower-right corner index of a Patch."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return lrcorner(self.patch.evaluate(**kwargs))


@dataclass
@weight(42)
class Crop(GridExpression):
    """Crops a subgrid from a grid."""

    grid: GridExpression
    start: TupleExpression
    dims: TupleExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return crop(self.grid.evaluate(**kwargs), self.start.evaluate(**kwargs), self.dims.evaluate(**kwargs))


@dataclass
@weight(36)
class Toindices(IndicesExpression):
    """Converts a Patch to a set of indices."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Indices:
        return toindices(self.patch.evaluate(**kwargs))


@dataclass
@weight(61)
class Recolor(ObjectExpression):
    """Recolors a patch to a new uniform color."""

    value: IntegerExpression
    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Object:
        return recolor(self.value.evaluate(**kwargs), self.patch.evaluate(**kwargs))


@dataclass
@weight(153)
class Shift(PatchExpression):
    """Shifts a patch by a given vector."""

    patch: PatchExpression
    directions: TupleExpression

    def evaluate(self, *args, **kwargs) -> Patch:
        return shift(self.patch.evaluate(**kwargs), self.directions.evaluate(**kwargs))


@dataclass
@weight(48)
class Normalize(PatchExpression):
    """Moves a patch's upper-left corner to the origin (0,0)."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Patch:
        return normalize(self.patch.evaluate(**kwargs))


@dataclass
@weight(15)
class Dneighbors(IndicesExpression):
    """Gets the four directly adjacent (cardinal) neighbors of a location."""

    loc: TupleExpression

    def evaluate(self, *args, **kwargs) -> Indices:
        return dneighbors(self.loc.evaluate(**kwargs))


@dataclass
@weight(5)
class Ineighbors(IndicesExpression):
    """Gets the four diagonally adjacent neighbors of a location."""

    loc: TupleExpression

    def evaluate(self, *args, **kwargs) -> Indices:
        return ineighbors(self.loc.evaluate(**kwargs))


@dataclass
@weight(53)
class Neighbors(IndicesExpression):
    """Gets all eight adjacent neighbors of a location."""

    loc: TupleExpression

    def evaluate(self, *args, **kwargs) -> Indices:
        return neighbors(self.loc.evaluate(**kwargs))


@dataclass
@weight(237)
class ObjectsFromGrid(ObjectsExpression):
    """Extracts objects from a grid based on connectivity rules."""

    grid: GridExpression
    univalued: BooleanExpression
    diagonal: BooleanExpression
    without_bg: BooleanExpression

    def evaluate(self, *args, **kwargs) -> Objects:
        return objects(
            self.grid.evaluate(**kwargs),
            self.univalued.evaluate(**kwargs),
            self.diagonal.evaluate(**kwargs),
            self.without_bg.evaluate(**kwargs),
        )


@dataclass
@weight(26)
class Partition(ObjectsExpression):
    """Partitions a grid into objects based on color, including background."""

    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Objects:
        return partition(self.grid.evaluate(**kwargs))


@dataclass
@weight(16)
class Fgpartition(ObjectsExpression):
    """Partitions a grid into objects based on color, excluding background."""

    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Objects:
        return fgpartition(self.grid.evaluate(**kwargs))


@dataclass
@weight(23)
class Uppermost(IntegerExpression):
    """Gets the minimum row index of a patch."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return uppermost(self.patch.evaluate(**kwargs))


@dataclass
@weight(7)
class Lowermost(IntegerExpression):
    """Gets the maximum row index of a patch."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return lowermost(self.patch.evaluate(**kwargs))


@dataclass
@weight(18)
class Leftmost(IntegerExpression):
    """Gets the minimum column index of a patch."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return leftmost(self.patch.evaluate(**kwargs))


@dataclass
@weight(6)
class Rightmost(IntegerExpression):
    """Gets the maximum column index of a patch."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return rightmost(self.patch.evaluate(**kwargs))


@dataclass
@weight(5)
class Square(BooleanExpression):
    """Checks if a piece is a square."""

    piece: PieceExpression

    def evaluate(self, *args, **kwargs) -> Boolean:
        return square(self.piece.evaluate(**kwargs))


@dataclass
@weight(18)
class Vline(BooleanExpression):
    """Checks if a patch is a vertical line."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Boolean:
        return vline(self.patch.evaluate(**kwargs))


@dataclass
@weight(16)
class Hline(BooleanExpression):
    """Checks if a patch is a horizontal line."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Boolean:
        return hline(self.patch.evaluate(**kwargs))


@dataclass
@weight(4)
class Hmatching(BooleanExpression):
    """Checks if two patches share any row indices."""

    a: PatchExpression
    b: PatchExpression

    def evaluate(self, *args, **kwargs) -> Boolean:
        return hmatching(self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(7)
class Vmatching(BooleanExpression):
    """Checks if two patches share any column indices."""

    a: PatchExpression
    b: PatchExpression

    def evaluate(self, *args, **kwargs) -> Boolean:
        return vmatching(self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(11)
class Manhattan(IntegerExpression):
    """Calculates the closest Manhattan distance between two patches."""

    a: PatchExpression
    b: PatchExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return manhattan(self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(10)
class Adjacent(BooleanExpression):
    """Checks if two patches are cardinally adjacent."""

    a: PatchExpression
    b: PatchExpression

    def evaluate(self, *args, **kwargs) -> Boolean:
        return adjacent(self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(10)
class Bordering(BooleanExpression):
    """Checks if a patch touches the border of a grid."""

    patch: PatchExpression
    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Boolean:
        return bordering(self.patch.evaluate(**kwargs), self.grid.evaluate(**kwargs))


@dataclass
@weight(3)
class Centerofmass(TupleExpression):
    """Calculates the center of mass of a patch."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return centerofmass(self.patch.evaluate(**kwargs))


@dataclass
@weight(32)
class Palette(FrozenSetExpression):
    """Gets the set of colors in an Element."""

    element: ElementExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return palette(self.element.evaluate(**kwargs))


@dataclass
@weight(23)
class Numcolors(IntegerExpression):
    """Counts the number of unique colors in an Element."""

    element: ElementExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return numcolors(self.element.evaluate(**kwargs))


@dataclass
@weight(495)
class Color(IntegerExpression):
    """Gets the color of a univalued object."""

    obj: ObjectExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return color(self.obj.evaluate(**kwargs))


@dataclass
@weight(24)
class Toobject(ObjectExpression):
    """Creates an object from a patch using colors from a grid."""

    patch: PatchExpression
    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Object:
        return toobject(self.patch.evaluate(**kwargs), self.grid.evaluate(**kwargs))


@dataclass
@weight(31)
class Asobject(ObjectExpression):
    """Converts an entire grid into a single object."""

    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Object:
        return asobject(self.grid.evaluate(**kwargs))


@dataclass
@weight(24)
class Rot90(GridExpression):
    """Rotates a grid 90 degrees clockwise."""

    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return rot90(self.grid.evaluate(**kwargs))


@dataclass
@weight(14)
class Rot180(GridExpression):
    """Rotates a grid 180 degrees."""

    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return rot180(self.grid.evaluate(**kwargs))


@dataclass
@weight(15)
class Rot270(GridExpression):
    """Rotates a grid 270 degrees clockwise."""

    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return rot270(self.grid.evaluate(**kwargs))


@dataclass
@weight(39)
class HmirrorGrid(GridExpression):
    """Mirrors a grid horizontally."""

    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return hmirror(self.grid.evaluate(**kwargs))
    
@dataclass
@weight(39)
class HmirrorPatch(PatchExpression):
    """Mirrors a patch horizontally."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Patch:
        return hmirror(self.patch.evaluate(**kwargs))


@dataclass
@weight(47)
class VmirrorGrid(GridExpression):
    """Mirrors a grid vertically."""

    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return vmirror(self.grid.evaluate(**kwargs))
    
@dataclass
@weight(47)
class VmirrorPatch(PatchExpression):
    """Mirrors a patch vertically."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Patch:
        return vmirror(self.patch.evaluate(**kwargs))


@dataclass
@weight(35)
class DmirrorGrid(GridExpression):
    """Mirrors a grid along the main diagonal."""

    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return dmirror(self.grid.evaluate(**kwargs))
    
@dataclass
@weight(35)
class DmirrorPatch(PatchExpression):
    """Mirrors a patch along the main diagonal."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Patch:
        return dmirror(self.patch.evaluate(**kwargs))


@dataclass
@weight(13)
class CmirrorGrid(GridExpression):
    """Mirrors a grid along the anti-diagonal."""

    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return cmirror(self.grid.evaluate(**kwargs))
    
@dataclass
@weight(13)
class CmirrorPatch(PatchExpression):
    """Mirrors a patch along the anti-diagonal."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Patch:
        return cmirror(self.patch.evaluate(**kwargs))


@dataclass
@weight(287)
class Fill(GridExpression):
    """Fills a patch of a grid with a uniform color."""

    grid: GridExpression
    value: IntegerExpression
    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return fill(self.grid.evaluate(**kwargs), self.value.evaluate(**kwargs), self.patch.evaluate(**kwargs))


@dataclass
@weight(148)
class Paint(GridExpression):
    """Paints an object onto a grid."""

    grid: GridExpression
    obj: ObjectExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return paint(self.grid.evaluate(**kwargs), self.obj.evaluate(**kwargs))


@dataclass
@weight(35)
class Underfill(GridExpression):
    """Fills a patch of a grid with a color, but only on background cells."""

    grid: GridExpression
    value: IntegerExpression
    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return underfill(self.grid.evaluate(**kwargs), self.value.evaluate(**kwargs), self.patch.evaluate(**kwargs))


@dataclass
@weight(3)
class Underpaint(GridExpression):
    """Paints an object onto a grid, but only on background cells."""

    grid: GridExpression
    obj: ObjectExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return underpaint(self.grid.evaluate(**kwargs), self.obj.evaluate(**kwargs))


@dataclass
@weight(8)
class Hupscale(GridExpression):
    """Upscales a grid horizontally by a given factor."""

    grid: GridExpression
    factor: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return hupscale(self.grid.evaluate(**kwargs), self.factor.evaluate(**kwargs))


@dataclass
@weight(5)
class Vupscale(GridExpression):
    """Upscales a grid vertically by a given factor."""

    grid: GridExpression
    factor: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return vupscale(self.grid.evaluate(**kwargs), self.factor.evaluate(**kwargs))


@dataclass
@weight(42)
class UpscaleGrid(GridExpression):
    """Upscales a grid by a given factor."""

    grid: GridExpression
    factor: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return upscale(self.grid.evaluate(**kwargs), self.factor.evaluate(**kwargs))
    
@dataclass
@weight(42)
class UpscaleObject(ObjectExpression):
    """Upscales an object by a given factor."""

    object: ObjectExpression
    factor: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Object:
        return upscale(self.object.evaluate(**kwargs), self.factor.evaluate(**kwargs))


@dataclass
@weight(9)
class Downscale(GridExpression):
    """Downscales a grid by a given factor."""

    grid: GridExpression
    factor: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return downscale(self.grid.evaluate(**kwargs), self.factor.evaluate(**kwargs))


@dataclass
@weight(38)
class Hconcat(GridExpression):
    """Concatenates two grids horizontally."""

    a: GridExpression
    b: GridExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return hconcat(self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(47)
class Vconcat(GridExpression):
    """Concatenates two grids vertically."""

    a: GridExpression
    b: GridExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return vconcat(self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(66)
class Subgrid(GridExpression):
    """Extracts the smallest subgrid containing a patch."""

    patch: PatchExpression
    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return subgrid(self.patch.evaluate(**kwargs), self.grid.evaluate(**kwargs))


@dataclass
@weight(13)
class Hsplit(TupleExpression):
    """Splits a grid into N horizontal subgrids."""

    grid: GridExpression
    n: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Tuple:
        return hsplit(self.grid.evaluate(**kwargs), self.n.evaluate(**kwargs))


@dataclass
@weight(10)
class Vsplit(TupleExpression):
    """Splits a grid into N vertical subgrids."""

    grid: GridExpression
    n: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Tuple:
        return vsplit(self.grid.evaluate(**kwargs), self.n.evaluate(**kwargs))


@dataclass
@weight(6)
class Cellwise(GridExpression):
    """Compares two grids cell by cell, keeping matched values."""

    a: GridExpression
    b: GridExpression
    fallback: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return cellwise(self.a.evaluate(**kwargs), self.b.evaluate(**kwargs), self.fallback.evaluate(**kwargs))


@dataclass
@weight(64)
class Replace(GridExpression):
    """Replaces all occurrences of one color with another."""

    grid: GridExpression
    replacee: IntegerExpression
    replacer: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return replace(self.grid.evaluate(**kwargs), self.replacee.evaluate(**kwargs), self.replacer.evaluate(**kwargs))


@dataclass
@weight(12)
class Switch(GridExpression):
    """Swaps two colors in a grid."""

    grid: GridExpression
    a: IntegerExpression
    b: IntegerExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return switch(self.grid.evaluate(**kwargs), self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(47)
class Center(TupleExpression):
    """Calculates the geometric center of a patch."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return center(self.patch.evaluate(**kwargs))


@dataclass
@weight(7)
class Position(TupleExpression):
    """Calculates the relative position vector between two patches."""

    a: PatchExpression
    b: PatchExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return position(self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(14)
class Index(IntegerExpression):
    """Gets the color at a specific location in a grid."""

    grid: GridExpression
    loc: TupleExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return index(self.grid.evaluate(**kwargs), self.loc.evaluate(**kwargs))


@dataclass
@weight(64)
class Canvas(GridExpression):
    """Creates a new grid of a given size and color."""

    value: IntegerExpression
    dimensions: TupleExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return canvas(self.value.evaluate(**kwargs), self.dimensions.evaluate(**kwargs))


@dataclass
@weight(9)
class Corners(IndicesExpression):
    """Gets the four corner indices of a patch's bounding box."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Indices:
        return corners(self.patch.evaluate(**kwargs))


@dataclass
@weight(42)
class Connect(IndicesExpression):
    """Draws a line between two points."""

    a: TupleExpression
    b: TupleExpression

    def evaluate(self, *args, **kwargs) -> Indices:
        return connect(self.a.evaluate(**kwargs), self.b.evaluate(**kwargs))


@dataclass
@weight(23)
class Cover(GridExpression):
    """Removes a patch from a grid by filling it with the background color."""

    grid: GridExpression
    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return cover(self.grid.evaluate(**kwargs), self.patch.evaluate(**kwargs))


@dataclass
@weight(7)
class Trim(GridExpression):
    """Trims the outermost border of a grid."""

    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return trim(self.grid.evaluate(**kwargs))


@dataclass
@weight(46)
class Move(GridExpression):
    """Moves an object on a grid by a given offset."""

    grid: GridExpression
    obj: ObjectExpression
    offset: TupleExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return move(self.grid.evaluate(**kwargs), self.obj.evaluate(**kwargs), self.offset.evaluate(**kwargs))


@dataclass
@weight(19)
class Tophalf(GridExpression):
    """Gets the top half of a grid."""

    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return tophalf(self.grid.evaluate(**kwargs))


@dataclass
@weight(16)
class Bottomhalf(GridExpression):
    """Gets the bottom half of a grid."""

    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return bottomhalf(self.grid.evaluate(**kwargs))


@dataclass
@weight(16)
class Lefthalf(GridExpression):
    """Gets the left half of a grid."""

    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return lefthalf(self.grid.evaluate(**kwargs))


@dataclass
@weight(12)
class Righthalf(GridExpression):
    """Gets the right half of a grid."""

    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return righthalf(self.grid.evaluate(**kwargs))


@dataclass
@weight(18)
class Vfrontier(IndicesExpression):
    """Gets the vertical line passing through a location."""

    location: TupleExpression

    def evaluate(self, *args, **kwargs) -> Indices:
        return vfrontier(self.location.evaluate(**kwargs))


@dataclass
@weight(17)
class Hfrontier(IndicesExpression):
    """Gets the horizontal line passing through a location."""

    location: TupleExpression

    def evaluate(self, *args, **kwargs) -> Indices:
        return hfrontier(self.location.evaluate(**kwargs))


@dataclass
@weight(17)
class Backdrop(IndicesExpression):
    """Gets all indices within the bounding box of a patch."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Indices:
        return backdrop(self.patch.evaluate(**kwargs))


@dataclass
@weight(14)
class Delta(IndicesExpression):
    """Gets indices in the bounding box but not in the patch itself."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Indices:
        return delta(self.patch.evaluate(**kwargs))


@dataclass
@weight(11)
class Gravitate(TupleExpression):
    """Calculates the vector to move a source patch until adjacent to a destination."""

    source: PatchExpression
    destination: PatchExpression

    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return gravitate(self.source.evaluate(**kwargs), self.destination.evaluate(**kwargs))


@dataclass
@weight(12)
class Inbox(IndicesExpression):
    """Gets the inner box one step inside a patch's bounding box."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Indices:
        return inbox(self.patch.evaluate(**kwargs))


@dataclass
@weight(26)
class Outbox(IndicesExpression):
    """Gets the outer box one step outside a patch's bounding box."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Indices:
        return outbox(self.patch.evaluate(**kwargs))


@dataclass
@weight(53)
class Box(IndicesExpression):
    """Gets the outline of a patch's bounding box."""

    patch: PatchExpression

    def evaluate(self, *args, **kwargs) -> Indices:
        return box(self.patch.evaluate(**kwargs))


@dataclass
@weight(59)
class Shoot(IndicesExpression):
    """Projects a line from a start point in a given direction."""

    start: TupleExpression
    direction: TupleExpression

    def evaluate(self, *args, **kwargs) -> Indices:
        return shoot(self.start.evaluate(**kwargs), self.direction.evaluate(**kwargs))


@dataclass
@weight(21)
class Occurrences(IndicesExpression):
    """Finds all locations of an object within a grid."""

    grid: GridExpression
    obj: ObjectExpression

    def evaluate(self, *args, **kwargs) -> Indices:
        return occurrences(self.grid.evaluate(**kwargs), self.obj.evaluate(**kwargs))


@dataclass
@weight(4)
class Frontiers(ObjectsExpression):
    """Finds all single-colored horizontal and vertical lines in a grid."""

    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Objects:
        return frontiers(self.grid.evaluate(**kwargs))


@dataclass
@weight(6)
class Compress(GridExpression):
    """Removes all single-colored rows and columns (frontiers) from a grid."""

    grid: GridExpression

    def evaluate(self, *args, **kwargs) -> Grid:
        return compress(self.grid.evaluate(**kwargs))


@dataclass
@weight(7)
class Hperiod(IntegerExpression):
    """Calculates the horizontal periodicity of an object."""

    obj: ObjectExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return hperiod(self.obj.evaluate(**kwargs))


@dataclass
@weight(6)
class Vperiod(IntegerExpression):
    """Calculates the vertical periodicity of an object."""

    obj: ObjectExpression

    def evaluate(self, *args, **kwargs) -> Integer:
        return vperiod(self.obj.evaluate(**kwargs))


# ======================================================================================
# Constant Classes
# ======================================================================================


@dataclass
@weight(257)
class FalseConstant(BooleanExpression):
    def evaluate(self, *args, **kwargs) -> Boolean:
        return False

    def __str__(self):
        return "False"


@dataclass
@weight(454)
class TrueConstant(BooleanExpression):
    def evaluate(self, *args, **kwargs) -> Boolean:
        return True

    def __str__(self):
        return "True"


@dataclass
@weight(230)
class ZeroConstant(IntegerExpression):
    def evaluate(self, *args, **kwargs) -> Integer:
        return 0

    def __str__(self):
        return "0"


@dataclass
@weight(186)
class OneConstant(IntegerExpression):
    def evaluate(self, *args, **kwargs) -> Integer:
        return 1

    def __str__(self):
        return "1"


@dataclass
@weight(196)
class TwoConstant(IntegerExpression):
    def evaluate(self, *args, **kwargs) -> Integer:
        return 2

    def __str__(self):
        return "2"


@dataclass
@weight(133)
class ThreeConstant(IntegerExpression):
    def evaluate(self, *args, **kwargs) -> Integer:
        return 3

    def __str__(self):
        return "3"


@dataclass
@weight(82)
class FourConstant(IntegerExpression):
    def evaluate(self, *args, **kwargs) -> Integer:
        return 4

    def __str__(self):
        return "4"


@dataclass
@weight(83)
class FiveConstant(IntegerExpression):
    def evaluate(self, *args, **kwargs) -> Integer:
        return 5

    def __str__(self):
        return "5"


@dataclass
@weight(28)
class SixConstant(IntegerExpression):
    def evaluate(self, *args, **kwargs) -> Integer:
        return 6

    def __str__(self):
        return "6"


@dataclass
@weight(17)
class SevenConstant(IntegerExpression):
    def evaluate(self, *args, **kwargs) -> Integer:
        return 7

    def __str__(self):
        return "7"


@dataclass
@weight(78)
class EightConstant(IntegerExpression):
    def evaluate(self, *args, **kwargs) -> Integer:
        return 8

    def __str__(self):
        return "8"


@dataclass
@weight(31)
class NineConstant(IntegerExpression):
    def evaluate(self, *args, **kwargs) -> Integer:
        return 9

    def __str__(self):
        return "9"


@dataclass
@weight(14)
class TenConstant(IntegerExpression):
    def evaluate(self, *args, **kwargs) -> Integer:
        return 10

    def __str__(self):
        return "10"


@dataclass
@weight(10)
class NegOneConstant(IntegerExpression):
    def evaluate(self, *args, **kwargs) -> Integer:
        return -1

    def __str__(self):
        return "-1"


@dataclass
@weight(8)
class NegTwoConstant(IntegerExpression):
    def evaluate(self, *args, **kwargs) -> Integer:
        return -2

    def __str__(self):
        return "-2"


@dataclass
@weight(24)
class DownConstant(TupleExpression):
    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return (1, 0)

    def __str__(self):
        return "(1,0)"


@dataclass
@weight(13)
class RightConstant(TupleExpression):
    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return (0, 1)

    def __str__(self):
        return "(0,1)"


@dataclass
@weight(8)
class UpConstant(TupleExpression):
    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return (-1, 0)

    def __str__(self):
        return "(-1,0)"


@dataclass
@weight(6)
class LeftConstant(TupleExpression):
    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return (0, -1)

    def __str__(self):
        return "(0,-1)"


@dataclass
@weight(47)
class OriginConstant(TupleExpression):
    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return (0, 0)

    def __str__(self):
        return "(0,0)"


@dataclass
@weight(43)
class UnityConstant(TupleExpression):
    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return (1, 1)

    def __str__(self):
        return "(1,1)"


@dataclass
@weight(15)
class NegUnityConstant(TupleExpression):
    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return (-1, -1)

    def __str__(self):
        return "(-1,-1)"


@dataclass
@weight(13)
class UpRightConstant(TupleExpression):
    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return (-1, 1)

    def __str__(self):
        return "(-1,1)"


@dataclass
@weight(14)
class DownLeftConstant(TupleExpression):
    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return (1, -1)

    def __str__(self):
        return "(1,-1)"


@dataclass
@weight(9)
class ZeroByTwoConstant(TupleExpression):
    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return (0, 2)

    def __str__(self):
        return "(0,2)"


@dataclass
@weight(13)
class TwoByZeroConstant(TupleExpression):
    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return (2, 0)

    def __str__(self):
        return "(2,0)"


@dataclass
@weight(11)
class TwoByTwoConstant(TupleExpression):
    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return (2, 2)

    def __str__(self):
        return "(2,2)"


@dataclass
@weight(18)
class ThreeByThreeConstant(TupleExpression):
    def evaluate(self, *args, **kwargs) -> IntegerTuple:
        return (3, 3)

    def __str__(self):
        return "(3,3)"


# ======================================================================================
# Solver
# ======================================================================================


def create_program(expression: Expression) -> Callable:
    """
    Creates a callable function from an evolved expression tree.
    """

    def program(*args, **kwargs) -> Any:
        if "input_grid" not in kwargs and args:
            kwargs["input_grid"] = args[0]

        return expression.evaluate(**kwargs)

    return program


def pretty_print_program(expression: "Expression", indent_level: int = 0) -> str:
    """
    Recursively builds a clean, Python-like string representation of the
    expression tree with indentation, ignoring internal metadata.
    """
    if not any(isinstance(v, Expression) for v in getattr(expression, "__dict__", {}).values()):
        return str(expression)

    child_indent = "    " * (indent_level + 1)
    args = []

    for field, value in expression.__dict__.items():
        if field.startswith("gengy_"):
            continue

        if isinstance(value, Expression):
            arg_str = pretty_print_program(value, indent_level + 1)
            args.append(f"\n{child_indent}{field}={arg_str}")

    closing_indent = "    " * indent_level

    if not args:
        return f"{expression.__class__.__name__}()"
    else:
        return f"{expression.__class__.__name__}({''.join(args)}\n{closing_indent})"


def count_nodes(expression: Expression) -> int:
    """Recursively counts the number of nodes in an expression tree."""
    count = 1  # Count the current node
    for field, value in expression.__dict__.items():
        if isinstance(value, Expression):
            count += count_nodes(value)
    return count


def program_uses_input(expression: Expression) -> bool:
    """Recursively checks if the expression tree contains an InputGrid node."""
    if isinstance(expression, InputGrid):
        return True
    for field, value in expression.__dict__.items():
        if isinstance(value, Expression) and program_uses_input(value):
            return True
    return False


def solve_task(task_id: str, csv_file_path: str, max_depth: int = 5, population_size: int = 150, time_limit: int = 60):
    task = load_arc_task_by_id(task_id)

    grammar = extract_grammar(
        [   Expression,
            Identity,
            AddInteger,
            AddTuple,
            SubtractInteger,
            SubtractTuple,
            MultiplyInteger,
            MultiplyTuple,
            DivideInteger,
            DivideTuple,
            InvertInteger,
            InvertTuple,
            Even,
            DoubleInteger,
            DoubleTuple,
            HalveInteger,
            HalveTuple,
            Flip,
            Equality,
            Contained,
            Combine,
            Intersection,
            Difference,
            Dedupe,
            Order,
            Repeat,
            Greater,
            Size,
            Merge,
            Maximum,
            Minimum,
            Valmax,
            Valmin,
            Argmax,
            Argmin,
            MostCommon,
            LeastCommon,
            Initset,
            Both,
            Either,
            IncrementInteger,
            IncrementTuple,
            DecrementInteger,
            DecrementTuple,
            CrementInteger,
            CrementTuple,
            SignInteger,
            SignTuple,
            Positive,
            Toivec,
            Tojvec,
            Sfilter,
            Mfilter,
            Extract,
            Totuple,
            First,
            Last,
            Insert,
            Remove,
            Other,
            Interval,
            Astuple,
            Product,
            Pair,
            Branch,
            Compose,
            Chain,
            Matcher,
            Rbind,
            Lbind,
            Power,
            Fork,
            Apply,
            Rapply,
            Mapply,
            Papply,
            Mpapply,
            Prapply,
            Mostcolor,
            Leastcolor,
            Height,
            Width,
            Shape,
            Portrait,
            Colorcount,
            Colorfilter,
            Sizefilter,
            Asindices,
            Ofcolor,
            Ulcorner,
            Urcorner,
            Llcorner,
            Lrcorner,
            Crop,
            Toindices,
            Recolor,
            Shift,
            Normalize,
            Dneighbors,
            Ineighbors,
            Neighbors,
            ObjectsFromGrid,
            Partition,
            Fgpartition,
            Uppermost,
            Lowermost,
            Leftmost,
            Rightmost,
            Square,
            Vline,
            Hline,
            Hmatching,
            Vmatching,
            Manhattan,
            Adjacent,
            Bordering,
            Centerofmass,
            Palette,
            Numcolors,
            Color,
            Toobject,
            Asobject,
            Rot90,
            Rot180,
            Rot270,
            HmirrorGrid,
            VmirrorGrid,
            HmirrorPatch,
            VmirrorPatch,
            CmirrorGrid,
            CmirrorPatch,
            DmirrorGrid,
            DmirrorPatch,
            Fill,
            Paint,
            Underfill,
            Underpaint,
            Hupscale,
            Vupscale,
            UpscaleGrid,
            UpscaleObject,
            Downscale,
            Hconcat,
            Vconcat,
            Subgrid,
            Hsplit,
            Vsplit,
            Cellwise,
            Replace,
            Switch,
            Center,
            Position,
            Index,
            Canvas,
            Corners,
            Connect,
            Cover,
            Trim,
            Move,
            Tophalf,
            Bottomhalf,
            Lefthalf,
            Righthalf,
            Vfrontier,
            Hfrontier,
            Backdrop,
            Delta,
            Gravitate,
            Inbox,
            Outbox,
            Box,
            Shoot,
            Occurrences,
            Frontiers,
            Compress,
            Hperiod,
            Vperiod,
            FalseConstant,
            TrueConstant,
            ZeroConstant,
            OneConstant,
            TwoConstant,
            ThreeConstant,
            FourConstant,
            FiveConstant,
            SixConstant,
            SevenConstant,
            EightConstant,
            NineConstant,
            TenConstant,
            NegOneConstant,
            NegTwoConstant,
            DownConstant,
            RightConstant,
            UpConstant,
            LeftConstant,
            OriginConstant,
            UnityConstant,
            NegUnityConstant,
            UpRightConstant,
            DownLeftConstant,
            ZeroByTwoConstant,
            TwoByZeroConstant,
            TwoByTwoConstant,
            ThreeByThreeConstant,
            InputGrid,
        ],
        GridExpression,
    )

    def train_fitness_function(individual: GridExpression) -> float:
        program = create_program(individual)
        score = evaluate_on_train_impl(program, task)

        if score < 0.0:
            return -1

        # Heavily penalize programs that don't use the input grid
        if not program_uses_input(individual):
            return 0.001

        # Penalize trivial (single-color) solutions
        try:
            output_grid = program(input_grid=task.train[0].input)
            if len(palette(output_grid)) <= 1:
                score *= 0.1  # Reduce score by 90%
        except Exception:
            pass  # Ignore errors during penalty calculation

        # Apply a parsimony pressure for size
        parsimony_coefficient = 0.001  # A very small penalty
        penalty = count_nodes(individual) * parsimony_coefficient
        final_score = score - penalty

        return max(0, final_score)

    def test_fitness_function(individual: GridExpression) -> float:
        program = create_program(individual)
        return evaluate_on_test_impl(program, task)

    # Create the problem
    problem = SingleObjectiveProblem(fitness_function=train_fitness_function, minimize=False)

    # Configure GP parameters
    gp_params = {
        "population_size": population_size,
        "n_elites": 3,
        "novelty": 15,
        "probability_mutation": 0.15,
        "probability_crossover": 0.8,
        "tournament_size": 5,
        "timer_limit": time_limit,
    }

    # Create the GP step
    gp_step = ParallelStep(
        [
            ElitismStep(),
            NoveltyStep(),
            SequenceStep(
                TournamentSelection(gp_params["tournament_size"]),
                GenericCrossoverStep(gp_params["probability_crossover"]),
                GenericMutationStep(gp_params["probability_mutation"]),
            ),
        ],
        weights=[
            gp_params["n_elites"],
            gp_params["novelty"],
            gp_params["population_size"] - gp_params["n_elites"] - gp_params["novelty"],
        ],
    )

    # Create and run the algorithm
    alg = GeneticProgramming(
        problem=problem,
        budget=TimeBudget(time=gp_params["timer_limit"]),
        representation=TreeBasedRepresentation(
            grammar, decider=MaxDepthDecider(NativeRandomSource(42), grammar, max_depth=max_depth)
        ),
        random=NativeRandomSource(42),
        population_size=gp_params["population_size"],
        step=gp_step,
    )

    print(f"--- Starting search for task {task_id} ---")
    start_time = time.time()
    best_individuals = alg.search()
    end_time = time.time()
    
    time_taken = end_time - start_time

    # --- Result Handling and CSV Writing ---
    if not best_individuals:
        print(f"No solution found for task {task_id}")
        result_row = [task_id, 0.0, time_taken, "No solution found"]
    else:
        best_individual = best_individuals[0]
        final_program = create_program(best_individual.get_phenotype())
        test_fitness = evaluate_on_test_impl(final_program, task)
        solution_str = pretty_print_program(best_individual.get_phenotype())
        
        result_row = [task_id, test_fitness, time_taken, solution_str]
        print(f"--- Finished search for task {task_id}. Test Fitness: {test_fitness:.4f} ---")

    # Append the result to the CSV file
    with open(csv_file_path, 'a', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(result_row)


if __name__ == "__main__":
    # --- Command-Line Argument Parsing ---
    parser = argparse.ArgumentParser(description="Solve a specific ARC task and log results to CSV.")
    parser.add_argument("--task_id", required=True, type=str, help="The ID of the ARC task to solve.")
    parser.add_argument("--csv_file", default="arc_results.csv", type=str, help="Path to the output CSV file.")
    
    args = parser.parse_args()
    
    # Call the solver with the provided arguments
    solve_task(args.task_id, args.csv_file)
