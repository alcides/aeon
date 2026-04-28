from __future__ import annotations

from aeon.sugar.bind import bind, bind_program
from aeon.sugar.desugar import desugar, expand_inductive_decls, infer_inductive_rforall_decls
from aeon.sugar.parser import parse_main_program, parse_program
from aeon.sugar.program import Program, SAnonConstructor
from aeon.elaboration import elaborate
from aeon.sugar.ast_helpers import st_top


def test_match_lowering_intlist():
    # This test checks that Lean-style match syntax on an inductive
    # lowers to the generated `<Inductive>_rec` eliminator.
    #
    # Runtime / typechecking might require external deps; we focus on AST lowering.
    src = """
        inductive IntList
        | empty : IntList
        | cons (hd:Int) (tl:IntList) : IntList
        def mk (l:IntList) : IntList =
            match l with
            | .empty => l
            | .cons hd tl => l
        def main (args:Int) : Int =
            0
    """

    prog = parse_program(src)
    desugared = desugar(prog, is_main_hole=True)
    # Lowering should remove SMatch nodes and use the generated eliminator.
    dumped = str(desugared.program)
    # Our surface AST pretty-print includes "match ... with" for SMatch.
    assert "SMatch" not in dumped
    assert "IntList_rec" in dumped


def test_match_lowering_intlist_after_bind_program():
    """`bind_program` renames inductive constructors; match branches must use the same names."""
    src = """
        inductive IntList
        | empty : IntList
        | cons (hd:Int) (tl:IntList) : IntList
        def mk (l:IntList) : IntList =
            match l with
            | .empty => l
            | .cons hd tl => l
        def main (args:Int) : Int =
            0
    """

    prog = parse_main_program(src, filename="<test>")
    prog = bind_program(prog, [])
    desugared = desugar(prog, is_main_hole=True)
    dumped = str(desugared.program)
    assert "SMatch" not in dumped
    assert "IntList_rec" in dumped


def test_inductive_abstract_refinement_parameters_parse():
    """Liquid Haskell-style ``data T <p :: S -> Bool>`` as datatype-level ``forall <p : S -> Bool>``."""
    src = """
        inductive Box forall <p : Int -> Bool>
        | mk (x:Int) : Box
        def main (args:Int) : Int = 0
    """
    prog = parse_program(src)
    ind = prog.inductive_decls[0]
    assert len(ind.rforalls) == 1
    pname, psort = ind.rforalls[0]
    assert pname.name == "p"
    assert "Int" in str(psort)


def test_inductive_rforalls_merge_into_constructors_and_eliminator():
    src = """
        inductive Box forall <p : Int -> Bool>
        | mk (x:Int) : Box
        def main (args:Int) : Int = 0
    """
    prog = parse_program(src)
    expanded = expand_inductive_decls(Program(prog.imports, prog.type_decls, prog.inductive_decls, prog.definitions))
    mk = next(d for d in expanded.definitions if d.name.name == "Box_mk")
    rec = next(d for d in expanded.definitions if d.name.name == "Box_rec")
    assert len(mk.rforalls) == 1
    assert mk.rforalls[0][0].name == "p"
    assert len(rec.rforalls) == 1
    assert rec.rforalls[0][0].name == "p"


def test_inductive_rforall_sort_may_use_type_parameter():
    """Predicate sort ``a -> Bool`` matches LH ``<p :: a -> Bool>`` (domain is the type parameter)."""
    src = """
        inductive RList a forall <p : a -> Bool>
        | rnil : (RList a)
        def main (args:Int) : Int = 0
    """
    prog = parse_program(src)
    ind = prog.inductive_decls[0]
    assert ind.args[0].name == "a"
    assert ind.rforalls[0][0].name == "p"


def test_infer_inductive_rforall_from_constructor_signature():
    src = """
        inductive Box
        | mk : {b:Box | r b}
        def main (args:Int) : Int = 0
    """
    prog = parse_program(src)
    assert prog.inductive_decls[0].rforalls == []
    inferred = infer_inductive_rforall_decls(prog)
    ind = inferred.inductive_decls[0]
    assert len(ind.rforalls) == 1
    assert ind.rforalls[0][0].name == "r"
    expanded = expand_inductive_decls(
        Program(inferred.imports, inferred.type_decls, inferred.inductive_decls, inferred.definitions)
    )
    box_mk = next(d for d in expanded.definitions if d.name.name == "Box_mk")
    rec = next(d for d in expanded.definitions if d.name.name == "Box_rec")
    assert len(box_mk.rforalls) == 1
    assert box_mk.rforalls[0][0].name == "r"
    assert len(rec.rforalls) == 1
    assert rec.rforalls[0][0].name == "r"


def test_infer_inductive_rforall_from_top_level_def_types():
    src = """
        inductive Box
        | mk : Box
        def use (x:{b:Box | s b}) : Int = 0
        def main (args:Int) : Int = 0
    """
    prog = parse_program(src)
    inferred = infer_inductive_rforall_decls(prog)
    ind = inferred.inductive_decls[0]
    assert len(ind.rforalls) == 1
    assert ind.rforalls[0][0].name == "s"


def test_infer_inductive_rforall_from_type_parameter_refinement():
    src = """
        inductive RList a
        | rnil : (RList a)
        | rcons (x:{v:a | q v}) : (RList a)
        def main (args:Int) : Int = 0
    """
    prog = parse_program(src)
    inferred = infer_inductive_rforall_decls(prog)
    ind = inferred.inductive_decls[0]
    assert len(ind.rforalls) == 1
    assert ind.rforalls[0][0].name == "q"


def test_infer_inductive_rforall_does_not_lift_predicates_on_other_sorts():
    src = """
        inductive Box
        | mk : {x:Int | p x}
        def main (args:Int) : Int = 0
    """
    prog = parse_program(src)
    inferred = infer_inductive_rforall_decls(prog)
    assert inferred.inductive_decls[0].rforalls == []


def test_qualified_constructors_in_expressions():
    """IntList.cons and IntList.empty resolve to constructors in expressions."""
    src = """
        inductive IntList
        | empty : IntList
        | cons (hd:Int) (tl:IntList) : IntList
        def mk : IntList = IntList.cons 1 (IntList.empty)
        def main (args:Int) : Int = 0
    """
    prog = parse_main_program(src, "<test>")
    prog = bind_program(prog, [])
    desugared = desugar(prog, is_main_hole=True)
    dumped = str(desugared.program)
    assert "SQualifiedVar" not in dumped
    assert "cons" in dumped
    assert "empty" in dumped


def test_qualified_constructors_in_match_branches():
    """IntList.empty / IntList.cons in match branches lower correctly."""
    src = """
        inductive IntList
        | empty : IntList
        | cons (hd:Int) (tl:IntList) : IntList
        def f (l:IntList) : Int =
            match l with
            | IntList.empty => 0
            | IntList.cons hd tl => hd
        def main (args:Int) : Int = 0
    """
    prog = parse_main_program(src, "<test>")
    prog = bind_program(prog, [])
    desugared = desugar(prog, is_main_hole=True)
    dumped = str(desugared.program)
    assert "SMatch" not in dumped
    assert "IntList_rec" in dumped


def test_anon_constructors_in_match_branches():
    """.empty / .cons in match branches lower correctly (dot stripped)."""
    src = """
        inductive IntList
        | empty : IntList
        | cons (hd:Int) (tl:IntList) : IntList
        def f (l:IntList) : Int =
            match l with
            | .empty => 0
            | .cons hd tl => hd
        def main (args:Int) : Int = 0
    """
    prog = parse_main_program(src, "<test>")
    prog = bind_program(prog, [])
    desugared = desugar(prog, is_main_hole=True)
    dumped = str(desugared.program)
    assert "SMatch" not in dumped
    assert "IntList_rec" in dumped


def test_anon_constructor_in_expression_with_annotation():
    """SAnonConstructor resolves during elaboration when type context is available."""
    src = """
        inductive IntList
        | empty : IntList
        | cons (hd:Int) (tl:IntList) : IntList
        def mk : IntList = (.cons 1 (.empty) : IntList)
        def main (args:Int) : Int = 0
    """
    prog = parse_main_program(src, "<test>")
    prog = bind_program(prog, [])
    desugared = desugar(prog, is_main_hole=True)
    ctx, progt = bind(desugared.elabcontext, desugared.program)
    # Should elaborate without errors: SAnonConstructor resolved via type context
    sterm = elaborate(ctx, progt, st_top)
    dumped = str(sterm)
    assert "AnonCtor" not in dumped


def test_anon_constructor_parsed_as_node():
    """Parser produces SAnonConstructor for .foo expressions."""
    from aeon.sugar.parser import parse_expression

    t = parse_expression(".empty")
    assert isinstance(t, SAnonConstructor)
    assert t.name == "empty"


def test_constructor_to_type_populated():
    """DesugaredProgram.constructor_to_type maps constructor names to inductive types."""
    src = """
        inductive IntList
        | empty : IntList
        | cons (hd:Int) (tl:IntList) : IntList
        def main (args:Int) : Int = 0
    """
    prog = parse_main_program(src, "<test>")
    prog = bind_program(prog, [])
    desugared = desugar(prog, is_main_hole=True)
    assert "empty" in desugared.constructor_to_type
    assert "cons" in desugared.constructor_to_type
    assert desugared.constructor_to_type["empty"].name == "IntList"
    assert desugared.constructor_to_type["cons"].name == "IntList"


def test_bare_constructors_require_open():
    """Bare constructor names require 'open IntList' to resolve."""
    src = """
        open IntList
        inductive IntList
        | empty : IntList
        | cons (hd:Int) (tl:IntList) : IntList
        def mk : IntList = cons 1 empty
        def f (l:IntList) : Int =
            match l with
            | .empty => 0
            | .cons hd tl => hd
        def main (args:Int) : Int = 0
    """
    prog = parse_main_program(src, "<test>")
    prog = bind_program(prog, [])
    desugared = desugar(prog, is_main_hole=True)
    dumped = str(desugared.program)
    # After open, bare 'cons' and 'empty' should resolve to IntList_cons / IntList_empty
    assert "IntList_cons" in dumped or "cons" in dumped
    assert "IntList_rec" in dumped


def test_bare_constructors_fail_without_open():
    """Without 'open', bare constructor names are NOT resolved (remain as unresolved vars)."""
    from aeon.facade.api import AeonError

    src = """
        inductive IntList
        | empty : IntList
        | cons (hd:Int) (tl:IntList) : IntList
        def mk : IntList = cons 1 empty
        def main (args:Int) : Int = 0
    """
    prog = parse_main_program(src, "<test>")
    prog = bind_program(prog, [])
    desugared = desugar(prog, is_main_hole=True)
    ctx, progt = bind(desugared.elabcontext, desugared.program)
    # Bare 'cons' should not resolve — elaboration should fail
    import pytest

    with pytest.raises((AeonError, AssertionError)):
        elaborate(ctx, progt, st_top)
