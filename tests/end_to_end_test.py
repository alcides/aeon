from __future__ import annotations

from aeon.sugar.parser import parse_type
from aeon.sugar.stypes import SBaseType
from tests.driver import check_compile_expr

top = SBaseType("Top")


def test_anf():
    source = r"""let f : (x:Int) -> (y:Int) -> Int = (\x -> (\y -> x)) in
           let r = f (f 1 2) (f 2 3) in
           r"""
    assert check_compile_expr(source, top, 1)


def test_anf_typed():
    source = r"""let f : (x:Int) -> (y:Int) -> {z:Int | z == x } = (\x -> (\y -> x)) in
           let r = f (f 1 2) (f 2 3) in
           r"""
    assert check_compile_expr(source, top, 1)


def test_anf_typed_smaller():
    source = r"""let f : (x:Int) -> (y:Int) -> {z:Int | z == x } = (\x -> (\y -> x)) in
           f (f 3 4) 2"""

    source = "let x = 3 in x"
    assert check_compile_expr(source, parse_type("{x:Int | x == 3}"), 3)


def test_annotation():
    source = r""" (1 : Int) """
    assert check_compile_expr(source, parse_type("Int"), 1)


def test_annotation_anf():
    source = r"""let j = (let f : (x:Int) -> {y :Int | y == x} = \x -> x in
                          let a : {x:Int | x == 3} = 3 in
                          f a)
                in j"""
    assert check_compile_expr(source, parse_type("{x:Int | x == 3}"), 3)


def test_annotation_anf2():
    source = r"""let j : {x:Int | x == 3} = (let f : (x:Int) -> {y :Int | y == x} = \x -> x in let a : {x:Int | x == 3} = (let k : {x:Int | x == 3} = 3 in k) in f a) in j"""
    assert check_compile_expr(source, parse_type("{x:Int | x == 3}"), 3)


def test_annotation_anf3():
    source = r"""3 % 2"""
    assert check_compile_expr(source, parse_type("{x:Int | x == 1}"), 1)
