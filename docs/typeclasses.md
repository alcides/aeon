# Typeclasses

Aeon elaborates `class` and `instance` declarations into typed dictionaries.
A method call receives its dictionary automatically, selected by its full
instance type. Instance bodies are checked against the class's method types.

```aeon
class Eq (a:B) where
    eq : (x:a) -> (y:a) -> Bool;
    neq : (x:a) -> (y:a) -> Bool := fun x => fun y => !(eq x y);

instance : Eq Int where
    eq x y := x = y;

def same [Eq a] (x:a) (y:a) : Bool := eq x y;
def main (args:Int) : Bool := same 3 3;
```

Methods can have defaults, and an instance can override them. Instances can be
named (`instance intEq : Eq Int where ...`). Class and instance declarations
are collected from imported modules. Instance requirements such as
`instance [Eq a] : Eq (Box a)` are resolved recursively, including nested
containers. A lexical `[Eq a]` parameter supplies evidence inside a generic
function or constrained instance.

## Superclasses

```aeon
class Order (a:B) extends (Eq a) where
    lt : (x:a) -> (y:a) -> Bool;

instance : Order Int where
    lt x y := x < y;

def sameOrdered [Order a] (x:a) (y:a) : Bool := eq x y;
```

`Order Int` requires an `Eq Int` instance. Its dictionary stores that evidence,
and `[Order a]` makes `Eq a` available to generic code. This works transitively
and with multiple superclasses. Unknown superclasses, wrong arities, and
inheritance cycles are errors. Superclass instances may appear after subclass
instances in the source.

## Instance selection and coherence

Resolution compares all type arguments and their nested structure. Thus
`Pick Int Bool` and `Pick Int Int`, or `Tag (Box Int)` and `Tag (Box Bool)`, can
coexist. Repeated pattern variables must match the same complete type.

Overlapping instance heads are rejected, including duplicate named instances
and a generic instance that overlaps a concrete one. Constraints do not
establish a priority between overlapping heads. Resolution reports an error
for missing instances or recursive requirements that do not make progress;
it does not silently replace an earlier instance or recurse indefinitely.

## Higher-kinded parameters

Arrow kinds describe constructors. `B -> B` accepts a constructor with one
base-type parameter, such as `Box` or `List`; `(Pair Int)` is a partial
application with the same kind. A saturated type such as `Box Int` has kind
`B` and cannot be supplied in that position. `B` and `*` retain Aeon's
existing distinction between refinable base types and general value types.

```aeon
class Functor (f:B -> B) where
    fmap : forall a:B, forall b:B,
        (g:(x:a) -> b) -> (xs:(f a)) -> (f b);

instance : Functor Box where
    fmap g xs := match xs with | box x => Box.box (g x);

def increment [Functor f] (xs:(f Int)) : (f Int) :=
    fmap (fun x => x + 1) xs;
```

The instance method must work for every `a` and `b`; a body that always
returns `Box.box 0` fails to implement `fmap`. Constructor arguments can be
inferred from value arguments or provided explicitly, such as `fmap{Box}`.
Superclass dictionaries also support constructor parameters. The complete
[Functor/Monad example](../examples/syntax/higher_kinded_typeclasses.ae)
returns `7`.

## Refinement contracts and SMT reasoning

Put the guarantee needed by callers in the method signature:

```aeon
class ExactEq (a:B) where
    exactEq : (x:a) -> (y:a) -> {r:Bool | r = (x = y)};
```

Every instance implementation must prove this contract. The compiler then
uses it at calls through either a concrete instance or a generic dictionary.
It does not need to unfold an arbitrary implementation or assume an
unverified algebraic law.

`Num` and `Ord` include contracts connecting their methods to primitive
arithmetic and comparison, so this program verifies:

```aeon
open Num

def twice [Num a] (x:a) : {r:a | r = x + x} := add x x;
def main (args:Int) : {r:Int | r = 10} := twice 5;
```

An incorrect claim such as `{r:Int | r = 11}` is rejected. Use primitive
operators in logical predicates; calls in executable code retain the
refinements promised by the methods. Interfaces that omit a shape or other
property from their signatures, such as the current `Models` interfaces,
do not acquire that property implicitly from a concrete implementation.

## Synthesis

Typeclass adaptation is shared by the synthesis entry point. It specializes
dictionary-passing functions using types in the hole's scope, resolves their
dictionaries, and exposes ordinary typed components to the search backend.
Abstract type variables, constructor variables and partial applications such
as `Pair Int` participate according to their declared kinds. An `Int` is never
used to instantiate a parameter of kind `B -> B`.

For example, the [generic conversion problem](../examples/synthesis/typeclasses/convert.ae)
asks for a value of abstract type `b`:

```aeon
class Convert (a:B) (b:B) where
    convert : (x:a) -> b;

def applyConvert [Convert a b] (x:a) : b := ?body;
```

TDSyn can synthesize `convert x`, internally supplying the `Convert a b`
dictionary received by `applyConvert`. Run the complete example with:

```sh
uv run python -m aeon --budget 10 -s tdsyn examples/synthesis/typeclasses/convert.ae
uv run python -m aeon --budget 10 -s tdsyn_backward examples/synthesis/typeclasses/higher_kinded.ae
```

Resolution uses lexical dictionaries and their superclass evidence before
global instances. It also composes constrained instances, such as resolving
`Eq (Box (Box Int))` through `Eq (Box Int)` and `Eq Int`. Repeated instance
parameters must agree; cyclic or growing prerequisite chains stop. Generated
dictionary constructors are not used to invent missing instances. Hidden
bindings and the function currently being synthesized cannot supply evidence.

Method refinements remain on specialized components. Temporary search names
expand to Core type applications and dictionary applications before validation,
fitness evaluation, example probing and returning a solution, including joint
synthesis. Thus optimization scores and correctness checks see the actual
program, and no extra bindings are required to execute the result.

| Backend family | Typeclass integration |
| --- | --- |
| TDSyn variants, Synquid, FTA/AFTA, LTA/CATA, grammar search | Specialized method components; generic conversion is covered by end-to-end tests. Individual backends retain their existing higher-order and datatype restrictions. |
| AMaze | Calls on available inputs become scalar components; its expression language remains monomorphic `Int`/`Bool`. |
| Arborist | Uses the same scalar components and interprets compiler-generated dictionary field access. Method bodies must remain within its pure interpreted language. |
| Solver-only and source-generating backends | Retain their existing expression languages and source elaboration. This adapter does not turn a numeric solver into an arbitrary polymorphic program generator. |

Preparation uses the synthesis time budget. Its type universe consists of
in-scope types and their constructor prefixes; it does not enumerate arbitrary
nested type expressions. Scalar components can call methods on existing inputs,
while backends that support function components can build further applications.
