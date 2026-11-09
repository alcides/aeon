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
