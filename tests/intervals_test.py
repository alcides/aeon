from __future__ import annotations

from geneticengine.grammar import extract_grammar
from geneticengine.random.sources import NativeRandomSource
from geneticengine.representations.tree.treebased import random_node

from aeon.core.liquid import LiquidApp, LiquidVar, LiquidLiteralInt
from aeon.core.types import t_int, RefinedType
from aeon.synthesis_grammar.grammar import (
    create_class_from_ctx_var,
    find_class_by_name,
    process_type_name,
)


def get_grammar_nodes(ctx_var: tuple) -> tuple[list[type], type]:
    refined_ty = ctx_var[1]
    grammar_n = create_class_from_ctx_var(ctx_var, [])
    grammar_n, root = find_class_by_name("t_" + process_type_name(refined_ty),
                                         grammar_n, refined_ty)
    grammar_nodes = [
        node for node in grammar_n
        if not node.__name__.startswith(("refined_app", "app_", "literal_Int",
                                         "t_Int"))
    ]

    return grammar_nodes, root


def test_gt_zero():
    # (i:{g:Int | g > 0})
    refined_ty = RefinedType(
        "g", t_int,
        LiquidApp(">", [LiquidVar("g"), LiquidLiteralInt(0)]))
    ctx_var = ("i", refined_ty)

    grammar_nodes, root = get_grammar_nodes(ctx_var)
    g = extract_grammar(grammar_nodes, root)
    r = NativeRandomSource(seed=1)
    n = random_node(r, g, 4, root)

    assert isinstance(n, grammar_nodes[0])  # t_Refined_Int_greater_than_0
    assert n.value > 0
    assert isinstance(n, grammar_nodes[1])


def test_gt_zero2():
    # (i:{g:Int | 0 < g})
    refined_ty = RefinedType(
        "g", t_int,
        LiquidApp("<",
                  [LiquidLiteralInt(0), LiquidVar("g")]))
    ctx_var = ("i", refined_ty)

    grammar_nodes, root = get_grammar_nodes(ctx_var)
    g = extract_grammar(grammar_nodes, root)
    r = NativeRandomSource(seed=1)

    for _ in range(100):
        n = random_node(r, g, 4, root)
        assert isinstance(n, grammar_nodes[0])  # t_Refined_Int_greater_than_0
        assert n.value > 0
        assert isinstance(
            n, grammar_nodes[1])  # literal_Refined_Int_greater_than_0


def test_gt_zero_and_lt_ten():
    # (i:{g:Int | g > 0 && g < 10})
    refined_ty = RefinedType(
        "g",
        t_int,
        LiquidApp(
            "&&",
            [
                LiquidApp(">",
                          [LiquidVar("g"), LiquidLiteralInt(0)]),
                LiquidApp(
                    "<", [LiquidVar("g"), LiquidLiteralInt(10)]),
            ],
        ),
    )

    ctx_var = ("i", refined_ty)

    grammar_nodes, root = get_grammar_nodes(ctx_var)
    g = extract_grammar(grammar_nodes, root)
    r = NativeRandomSource(seed=1)
    for _ in range(100):
        n = random_node(r, g, 4, root)

        assert isinstance(n, grammar_nodes[0])
        assert 0 < n.value < 10
        assert isinstance(n, grammar_nodes[1])


def test_gt_zero_and_lt_ten_or_gt_twenty_and_lt_thirty():
    # (i:{g:Int | (g > 0 && g < 10) || (g > 20 && g < 30)})
    refined_ty = RefinedType(
        "g",
        t_int,
        LiquidApp(
            "||",
            [
                LiquidApp(
                    "&&",
                    [
                        LiquidApp(">", [LiquidVar("g"),
                                        LiquidLiteralInt(0)]),
                        LiquidApp("<", [LiquidVar("g"),
                                        LiquidLiteralInt(10)]),
                    ],
                ),
                LiquidApp(
                    "&&",
                    [
                        LiquidApp(">", [LiquidVar("g"),
                                        LiquidLiteralInt(20)]),
                        LiquidApp("<", [LiquidVar("g"),
                                        LiquidLiteralInt(30)]),
                    ],
                ),
            ],
        ),
    )

    ctx_var = ("i", refined_ty)

    grammar_nodes, root = get_grammar_nodes(ctx_var)
    g = extract_grammar(grammar_nodes, root)
    r = NativeRandomSource(seed=1)
    for _ in range(100):
        n = random_node(r, g, 4, root)

        assert isinstance(n, grammar_nodes[0])
        assert 0 < n.value < 10 or 20 < n.value < 30
        assert isinstance(n, grammar_nodes[1])


def test_lt_zero_or_gt_ten_and_lt_twenty_or_gt_thirty():
    # (i:{g:Int | (g < 0 || g > 10) && (g < 20 || g > 30)})  ==> ]-oo, 0[ U ]10 , 20[ U ]30 , +inf[

    refined_ty = RefinedType(
        "g",
        t_int,
        LiquidApp(
            "&&",
            [
                LiquidApp(
                    "||",
                    [
                        LiquidApp("<", [LiquidVar("g"),
                                        LiquidLiteralInt(0)]),
                        LiquidApp(">", [LiquidVar("g"),
                                        LiquidLiteralInt(10)]),
                    ],
                ),
                LiquidApp(
                    "||",
                    [
                        LiquidApp("<", [LiquidVar("g"),
                                        LiquidLiteralInt(20)]),
                        LiquidApp(">", [LiquidVar("g"),
                                        LiquidLiteralInt(30)]),
                    ],
                ),
            ],
        ),
    )

    ctx_var = ("i", refined_ty)

    grammar_nodes, root = get_grammar_nodes(ctx_var)
    g = extract_grammar(grammar_nodes, root)
    r = NativeRandomSource(seed=1)
    for _ in range(100):
        n = random_node(r, g, 4, root)

        assert isinstance(n, grammar_nodes[0])
        assert n.value < 0 or 10 < n.value < 20 or 30 < n.value
        assert isinstance(n, grammar_nodes[1])
