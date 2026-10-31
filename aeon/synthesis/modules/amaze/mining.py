"""Bounded frequent, alpha-normalized subtree/frontier patterns from train only."""

from __future__ import annotations

from collections import defaultdict
from .corpus import digest
from .grammar import Expr, Production, size
import json


def patterns(expression: Expr, max_nodes=12, max_parameters=3):
    from itertools import product

    def subtrees(e):
        yield e
        for child in e.children:
            yield from subtrees(child)

    def frontiers(e, depth):
        # A cut retains the original subtree as its equality key. This ties
        # repeated variables AND repeated compound parameters correctly.
        yield ("cut", e)
        if depth and e.children:
            for children in product(*(tuple(frontiers(c, depth - 1)) for c in e.children)):
                yield ("node", e, children)
        elif e.op == "const":
            yield ("node", e, ())

    found = set()
    for subtree in subtrees(expression):
        for index, frontier in enumerate(frontiers(subtree, 3)):
            if index >= 2048:
                break
            parameters: dict[Expr, int] = {}

            def abstract(node):
                e = node[1]
                if node[0] == "cut":
                    if e not in parameters:
                        parameters[e] = len(parameters)
                    return Expr("param", e.sort, value=parameters[e])
                return Expr(e.op, e.sort, tuple(abstract(c) for c in node[2]), e.value)

            template = abstract(frontier)
            if 0 < len(parameters) <= max_parameters and 1 + len(parameters) < size(template) <= max_nodes:
                found.add((template, tuple(e.sort for e in parameters)))
    return found


def mine(tasks, min_support=2, max_patterns=32):
    support = defaultdict(set)
    lineage = defaultdict(set)
    for task in tasks:
        if task.split != "train":
            raise ValueError("macro mining accepts training split only")
        for pattern in patterns(task.reference):
            support[pattern].add(task.group)
            lineage[pattern].add(task.id)
    records = []
    for (template, args), groups in support.items():
        if len(groups) < min_support:
            continue
        identifier = "macro:" + digest(json.dumps([args, template.data()], sort_keys=True).encode())[:16]
        records.append(
            {
                "id": identifier,
                "arguments": args,
                "result": template.sort,
                "cost": 1,
                "template": template.data(),
                "support_groups": sorted(groups),
                "origins": sorted(lineage[(template, args)]),
            }
        )
    return sorted(records, key=lambda r: (-len(r["support_groups"]), r["id"]))[:max_patterns]


def production(record):
    expr = Expr.read(record["template"])
    args = tuple(record["arguments"])
    if not record["id"].startswith("macro:") or not 0 < len(args) <= 3 or not 1 + len(args) < size(expr) <= 12:
        raise ValueError("invalid learned macro")
    return Production(record["id"], args, record["result"], expr, record["cost"])
