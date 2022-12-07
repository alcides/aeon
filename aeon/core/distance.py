from __future__ import annotations

import zss

from aeon.core.terms import Abstraction
from aeon.core.terms import Application
from aeon.core.terms import If
from aeon.core.terms import Let
from aeon.core.terms import Literal
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import Var


def term_children(t: Term):
    if isinstance(t, Application):
        return [t.fun, t.arg]
    elif isinstance(t, Abstraction):
        return [t.var_name, t.body]
    elif isinstance(t, Rec):
        return [t.var_name, t.var_value, t.body]  # Type?
    elif isinstance(t, Let):
        return [t.var_name, t.var_value, t.body]
    elif isinstance(t, If):
        return [t.cond, t.then, t.otherwise]
    return []


def term_label(t: Term):
    if isinstance(t, Literal):
        return str(t.value)
    elif isinstance(t, Var):
        return str(t.name)
    return type(t).__name__


def term_label_dist(s1: str, s2: str):
    if s1 == s2:
        return 0
    else:
        return 1


def distance_terms(t1: Term, t2: Term):
    return zss.simple_distance(t1, t2, term_children, term_label, term_label_dist)


def pairwise_distance(ts: list[Term]):
    s = 0
    for i in range(len(ts)):
        for j in range(i + 1, len(ts)):
            t1 = ts[i]
            t2 = ts[j]
            s += distance_terms(t1, t2)
    return s


def term_depth(t: Term):
    if isinstance(t, Application):
        return 1 + max(term_depth(t.fun), term_depth(t.arg))
    elif isinstance(t, Abstraction):
        return 1 + term_depth(t.body)
    elif isinstance(t, Rec):
        return 1 + max(term_depth(t.var_value), term_depth(t.body))
    elif isinstance(t, Let):
        return 1 + max(term_depth(t.var_value), term_depth(t.body))
    elif isinstance(t, If):
        return 1 + max(term_depth(t.cond), term_depth(t.then), term_depth(t.otherwise))
    else:
        return 1
