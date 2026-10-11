"""Train BUSTLE on searches over synthetic inputs (paper §3.1).

Run ``python -m aeon.synthesis.modules.bustle.train --output model.json``.
Targets are sampled from an unguided value bank, positives from the target's
proper subexpressions, and negatives from non-subexpressions of the same type.
Train/validation splitting is by whole search, never by individual row.
"""

from __future__ import annotations

import argparse
import random
import time
from typing import Any

import numpy as np

from aeon.core.terms import Literal, Var
from aeon.core.types import t_bool, t_int, t_string
from aeon.synthesis.modules.bustle.model import GuidanceModel
from aeon.synthesis.modules.bustle.search import Operation, SearchStats, Value, enumerate_values
from aeon.synthesis.modules.bustle.signatures import Scalar, task_signature, value_signature
from aeon.synthesis.modules.bustle.synthesizer import extract_constants
from aeon.utils.name import Name
from aeon.synthesis.modules.bustle.values import valid_value

TYPES = {"Int": t_int, "String": t_string, "Bool": t_bool}
TRAIN_SCHEMAS = {
    "List": {"List_nil": (), "List_cons": ("Int", "List")},
    "Tree": {"Tree_leaf": ("Int",), "Tree_branch": ("Tree", "Tree")},
}


def training_operations() -> list[Operation]:
    definitions = [
        ("upper", ("String",), "String", lambda a: a[0].upper()),
        ("lower", ("String",), "String", lambda a: a[0].lower()),
        ("trim", ("String",), "String", lambda a: a[0].strip()),
        ("length", ("String",), "Int", lambda a: len(a[0])),
        ("concat", ("String", "String"), "String", lambda a: a[0] + a[1]),
        ("contains", ("String", "String"), "Bool", lambda a: a[1] in a[0]),
        ("add", ("Int", "Int"), "Int", lambda a: a[0] + a[1]),
        ("sub", ("Int", "Int"), "Int", lambda a: a[0] - a[1]),
        ("less", ("Int", "Int"), "Bool", lambda a: a[0] < a[1]),
        ("equal", ("Int", "Int"), "Bool", lambda a: a[0] == a[1]),
    ]
    definitions.extend(
        [
            ("cons", ("Int", "List"), "List", lambda a: ("List_cons", a[0], a[1])),
            ("head", ("List",), "Int", lambda a: a[0][1]),
            ("tail", ("List",), "List", lambda a: a[0][2]),
            ("leaf", ("Int",), "Tree", lambda a: ("Tree_leaf", a[0])),
            ("branch", ("Tree", "Tree"), "Tree", lambda a: ("Tree_branch", a[0], a[1])),
            ("left", ("Tree",), "Tree", lambda a: a[0][1]),
            ("right", ("Tree",), "Tree", lambda a: a[0][2]),
        ]
    )
    return [Operation(Var(Name(name, 0)), args, ret, execute) for name, args, ret, execute in definitions]


def descendants(value: Value) -> list[Value]:
    result: list[Value] = []
    for child in value.children:
        result.append(child)
        result.extend(descendants(child))
    return result


def generate_search(rng: random.Random, index: int) -> tuple[list[tuple[int, ...]], list[int]]:
    key = ("Int", "String", "List", "Tree")[index % 4]
    arity = rng.randint(1, 3)
    if key == "String":
        words = ["ab", "Cd", "XYZ", "  q ", "12", "a b", "xy_z", "hello", "Z9", "pq"]
        columns: list[tuple[Scalar, ...]] = [tuple(rng.choice(words) for _ in range(4)) for _ in range(arity)]
    elif key == "Int":
        columns = [tuple(rng.randint(-8, 12) for _ in range(4)) for _ in range(arity)]
    else:

        def sample(level: int = 0) -> Scalar:
            if key == "List":
                return (
                    ("List_nil",)
                    if level >= 3 or rng.random() < 0.3
                    else ("List_cons", rng.randint(0, 5), sample(level + 1))
                )
            return (
                ("Tree_leaf", rng.randint(0, 5))
                if level >= 2 or rng.random() < 0.5
                else ("Tree_branch", sample(level + 1), sample(level + 1))
            )

        columns = [tuple(sample() for _ in range(4)) for _ in range(arity)]
    atoms = [Value(Var(Name(f"x{i}", 0)), key, values) for i, values in enumerate(columns)]
    for typ, constants in extract_constants(columns, ("",) * 4).items():
        atoms.extend(Value(Literal(v, TYPES[typ]), typ, (v,) * 4) for v in constants)
    atoms.append(Value(Var(Name("List_nil", 0)), "List", (("List_nil",),) * 4))
    stats = SearchStats()
    enumerate_values(
        atoms,
        training_operations(),
        columns,
        ("",) * 4,
        accept=lambda value: False,
        predict=None,
        deadline=float("inf"),
        max_weight=5,
        max_values=400,
        stats=stats,
        valid=lambda value, typ: valid_value(value, typ, TRAIN_SCHEMAS),
    )
    candidates = [v for v in stats.values if v.children and len(set(v.outputs)) > 1]
    rng.shuffle(candidates)
    features: list[tuple[int, ...]] = []
    labels: list[int] = []
    for target in candidates[:40]:
        positives = descendants(target)
        positive = rng.choice(positives)
        excluded = {(v.key, v.outputs) for v in [target, *positives]}
        negatives = [v for v in stats.values if v.key == positive.key and (v.key, v.outputs) not in excluded]
        if not negatives:
            continue
        signature = task_signature(columns, target.outputs)
        for value, label in ((positive, 1), (rng.choice(negatives), 0)):
            features.append(signature + value_signature(value.outputs, target.outputs))
            labels.append(label)
    return features, labels


def train(*, searches: int = 200, epochs: int = 40, seed: int = 0) -> GuidanceModel:
    if searches < 4 or epochs < 1:
        raise ValueError("training requires at least four searches and one epoch")
    rng = random.Random(seed)
    train_features: list[tuple[int, ...]] = []
    train_labels: list[int] = []
    validation_features: list[tuple[int, ...]] = []
    validation_labels: list[int] = []
    for index in range(searches):
        features, labels = generate_search(rng, index)
        if index % 5 == 0:
            validation_features.extend(features)
            validation_labels.extend(labels)
        else:
            train_features.extend(features)
            train_labels.extend(labels)
    model = GuidanceModel.initialize(seed)
    initial = model.predict(np.asarray(train_features))
    initial_loss = float(
        -np.mean(
            np.asarray(train_labels) * np.log(np.clip(initial, 1e-8, 1))
            + (1 - np.asarray(train_labels)) * np.log(np.clip(1 - initial, 1e-8, 1))
        )
    )
    losses = model.fit(np.asarray(train_features), np.asarray(train_labels), epochs=epochs, seed=seed)
    probabilities = model.predict(np.asarray(validation_features))
    validation_accuracy = float(np.mean((probabilities >= 0.5) == np.asarray(validation_labels)))
    provenance: dict[str, Any] = {
        "trained": True,
        "generator": "synthetic-bottom-up-search-scalar-adt-v2",
        "seed": seed,
        "searches": searches,
        "epochs": epochs,
        "input_families": {
            family: sum(i % 4 == n for i in range(searches))
            for n, family in enumerate(("Int", "String", "List", "Tree"))
        },
        "training_rows": len(train_labels),
        "validation_rows": len(validation_labels),
        "initial_training_loss": initial_loss,
        "final_training_loss": losses[-1],
        "validation_accuracy": validation_accuracy,
        "validation_split": "whole searches at indices divisible by five",
    }
    model.provenance = provenance
    return model


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True)
    parser.add_argument("--searches", type=int, default=200)
    parser.add_argument("--epochs", type=int, default=40)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    start = time.monotonic()
    model = train(searches=args.searches, epochs=args.epochs, seed=args.seed)
    model.save(args.output)
    print(model.provenance)
    print(f"Saved trained guidance to {args.output} ({time.monotonic() - start:.1f}s)")


if __name__ == "__main__":
    main()
