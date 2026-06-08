from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SynthesisUI

setup_logger()


def _run(source: str):
    cfg = AeonConfig(synthesizer="none", synthesis_ui=SynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(cfg)
    errors = list(driver.parse(aeon_code=source))
    assert not errors, errors
    return driver.run()


def _errors(source: str):
    cfg = AeonConfig(synthesizer="none", synthesis_ui=SynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(cfg)
    return list(driver.parse(aeon_code=source))


def test_instance_resolution_eq_int():
    source = r"""
    class Eq (a : B) where
        eq : (x : a) -> (y : a) -> Bool;

    instance : Eq Int where
        eq x y := x == y;

    def main (args : Int) : Int = if eq 3 3 then 0 else 1;
    """
    assert _run(source) == 0


def test_instance_resolution_eq_int_false_branch():
    source = r"""
    class Eq (a : B) where
        eq : (x : a) -> (y : a) -> Bool;

    instance : Eq Int where
        eq x y := x == y;

    def main (args : Int) : Int = if eq 3 4 then 100 else 200;
    """
    assert _run(source) == 200


def test_instance_dispatch_by_type():
    source = r"""
    class Eq (a : B) where
        eq : (x : a) -> (y : a) -> Bool;

    instance : Eq Int where
        eq x y := x == y;

    instance : Eq Bool where
        eq x y := if x then y else (if y then false else true);

    def main (args : Int) : Int =
        let a : Bool = eq 3 3 in
        let b : Bool = eq true false in
        if a then (if b then 1 else 2) else 3;
    """
    assert _run(source) == 2


def test_instance_dict_typechecks_standalone():
    source = r"""
    class Eq (a : B) where
        eq : (x : a) -> (y : a) -> Bool;

    instance : Eq Int where
        eq x y := x == y;

    def main (args : Int) : Int = 0;
    """
    assert _run(source) == 0


def test_missing_instance_is_error():
    source = r"""
    class Eq (a : B) where
        eq : (x : a) -> (y : a) -> Bool;

    instance : Eq Int where
        eq x y := x == y;

    def main (args : Int) : Int = if eq true true then 0 else 1;
    """
    assert _errors(source)


def test_refined_method_law_verifies():
    # The instance body satisfies the law in the refined method type, so SMT
    # discharges it and the program compiles + runs.
    source = r"""
    class Eq (a : B) where
        eq : (x : a) -> (y : a) -> {b : Bool | b == (x == y)};

    instance : Eq Int where
        eq x y := x == y;

    def main (args : Int) : Int = if eq 3 3 then 0 else 1;
    """
    assert _run(source) == 0


def test_default_method_used():
    # `neq` is not provided by the instance, so the class default body
    # (which itself calls `eq`) must be used — exercising a dictionary that
    # refers to itself through the default method.
    source = r"""
    class Eq (a : B) where
        eq : (x : a) -> (y : a) -> Bool;
        neq : (x : a) -> (y : a) -> Bool := fun x => fun y => if eq x y then false else true;

    instance : Eq Int where
        eq x y := x == y;

    def main (args : Int) : Int = if neq 3 4 then 100 else 200;
    """
    assert _run(source) == 100


def test_default_method_false_branch():
    source = r"""
    class Eq (a : B) where
        eq : (x : a) -> (y : a) -> Bool;
        neq : (x : a) -> (y : a) -> Bool := fun x => fun y => if eq x y then false else true;

    instance : Eq Int where
        eq x y := x == y;

    def main (args : Int) : Int = if neq 5 5 then 100 else 200;
    """
    assert _run(source) == 200


def test_default_method_overridden():
    # The instance provides its own `neq`, overriding the class default.
    source = r"""
    class Eq (a : B) where
        eq : (x : a) -> (y : a) -> Bool;
        neq : (x : a) -> (y : a) -> Bool := fun x => fun y => if eq x y then false else true;

    instance : Eq Int where
        eq x y := x == y;
        neq x y := if x == y then false else true;

    def main (args : Int) : Int = if neq 3 4 then 0 else 1;
    """
    assert _run(source) == 0


def test_refined_method_law_violation_is_error():
    # The instance body (`true`) violates the law `b == (x == y)`, so SMT
    # verification of the instance dictionary fails.
    source = r"""
    class Eq (a : B) where
        eq : (x : a) -> (y : a) -> {b : Bool | b == (x == y)};

    instance : Eq Int where
        eq x y := true;

    def main (args : Int) : Int = if eq 3 3 then 0 else 1;
    """
    assert _errors(source)


def test_constrained_instance_resolves():
    # `instance [Eq a] : Eq (Box a)` is resolved at the call site by unifying
    # `Box Int` against the pattern `Box a`, applying the type argument, and
    # threading the nested `Eq Int` dictionary as the constraint.
    source = r"""
    inductive Box a
    | box (v:a) : (Box a)

    class Eq (a : B) where
        eq : (x : a) -> (y : a) -> Bool;

    instance : Eq Int where
        eq x y := x == y;

    instance [Eq a] : Eq (Box a) where
        eq x y := eq (Box_rec x (fun v => v)) (Box_rec y (fun v => v));

    def main (args : Int) : Int = if eq (.box 3) (.box 3) then 0 else 1;
    """
    assert _run(source) == 0


def test_constrained_instance_dispatches_inner_eq():
    # The Box instance delegates to the element's `Eq` via the given
    # constraint, so `eq (.box 3) (.box 4)` must be false.
    source = r"""
    inductive Box a
    | box (v:a) : (Box a)

    class Eq (a : B) where
        eq : (x : a) -> (y : a) -> Bool;

    instance : Eq Int where
        eq x y := x == y;

    instance [Eq a] : Eq (Box a) where
        eq x y := eq (Box_rec x (fun v => v)) (Box_rec y (fun v => v));

    def main (args : Int) : Int =
        if eq (.box 3) (.box 3) then (if eq (.box 3) (.box 4) then 1 else 2) else 3;
    """
    assert _run(source) == 2


def test_nested_constrained_instance():
    # Resolution recurses: `Eq (Box (Box Int))` needs `Eq (Box Int)` needs
    # `Eq Int`, each supplied as a nested dictionary.
    source = r"""
    inductive Box a
    | box (v:a) : (Box a)

    class Eq (a : B) where
        eq : (x : a) -> (y : a) -> Bool;

    instance : Eq Int where
        eq x y := x == y;

    instance [Eq a] : Eq (Box a) where
        eq x y := eq (Box_rec x (fun v => v)) (Box_rec y (fun v => v));

    def main (args : Int) : Int =
        if eq (.box (.box 3)) (.box (.box 4)) then 10 else 20;
    """
    assert _run(source) == 20
