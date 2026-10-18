"""DENSER: synthesize a refined Aeon CNN and score it by measured validation accuracy.

Architecture construction and feasibility live in Denser.ae, not this backend.
The optional PyTorch dependency implements numerical training only. Dataset
downloads are explicit; search requires a local, train/validation-only NPZ.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import dataclasses
import json
import math
import os
from pathlib import Path
from typing import Any

import numpy as np
from lark.exceptions import UnexpectedInput

from aeon.core.terms import Let, Rec, Term, Var
from aeon.core.types import top
from aeon.errors import LiquidTypeCheckingFailedRelation
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.sugar.lifting import lift
from aeon.sugar.parser import parse_expression
from aeon.sugar.program import SApplication, SLiteral, SQualifiedVar, SVar
from aeon.synthesis.api import InvalidIndividualException, SynthesisNotSuccessful, Synthesizer
from aeon.synthesis.decorators import Goal
from aeon.synthesis.identification import get_holes_info, incomplete_functions_and_holes
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import ReflectedBinder, UninterpretedBinder, VariableBinder
from aeon.utils.name import Name
from aeon.utils.pprint import pretty_print_sterm

TASK_DIR = Path(__file__).resolve().parents[2] / "examples" / "synthesis" / "denser"
SOURCE_COMMIT = "8b4206d60a79e8da51f726a309fa1f4c924a4a90"
CONSTRUCTORS = {"input", "conv", "pool", "flatten", "dense", "softmax", "sgd", "adam", "rmsprop"}
ARITIES = {"input": 1, "conv": 8, "pool": 6, "flatten": 1, "dense": 4, "softmax": 1, "sgd": 7, "adam": 7, "rmsprop": 6}


def _int(value: Any, low: int, high: int) -> int:
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f"Expected integer in [{low}, {high}], got {value!r}")
    return value


def _float(value: Any, low: float, high: float, *, exclusive: bool = False) -> float:
    if type(value) is not float or not math.isfinite(value) or value < low or value > high:
        raise ValueError(f"Invalid floating-point parameter: {value!r}")
    if exclusive and value == high:
        raise ValueError("Optimizer coefficients must be strictly less than one")
    return value


@dataclasses.dataclass(frozen=True)
class Encoding:
    dataset: int
    layers: tuple[tuple, ...]
    learning: tuple
    parameters: int


def decode(candidate: Any) -> Encoding:
    """Check the numerical boundary independently; never repair/truncate a network."""
    chain = []
    node = candidate
    for _ in range(17):  # input + <=10 features + flatten + <=2 dense + head + learner
        if not isinstance(node, tuple) or not node or not isinstance(node[0], str):
            raise ValueError("Malformed Aeon architecture")
        if not node[0].startswith("Denser_"):
            raise ValueError("Expected a Denser constructor")
        tag = node[0].removeprefix("Denser_")
        if tag not in ARITIES or len(node) != ARITIES[tag] + 1:
            raise ValueError(f"Unknown or malformed constructor: {node[0]}")
        chain.append((tag, node[1:]))
        if tag == "input":
            break
        node = node[1]
    else:
        raise ValueError("Architecture exceeds the depth limit")
    chain.reverse()
    dataset = _int(chain[0][1][0], 0, 1)
    side, channels = (28, 1) if dataset == 0 else (32, 3)
    phase, features, hidden, params, width = 0, 0, 0, 0, 0
    layers: list[tuple] = []
    learning: tuple = ()
    for tag, args in chain[1:]:
        if tag in {"conv", "pool"}:
            if phase != 0 or features >= 10:
                raise ValueError("Features must precede flatten, with at most ten blocks")
            if tag == "conv":
                _, filters, kernel, stride, padding, act, bias, out = args
                _int(filters, 32, 256)
                _int(act, 0, 2)
                if type(bias) is not bool:
                    raise ValueError("Expected Boolean bias")
            else:
                _, kind, kernel, stride, padding, out = args
                _int(kind, 0, 1)
            _int(kernel, 2, 5)
            _int(stride, 1, 3)
            _int(padding, 0, 1)
            actual = (side + stride - 1) // stride if padding else (side - kernel) // stride + 1
            if (not padding and kernel > side) or type(out) is not int or out != actual or actual <= 0:
                raise ValueError("Invalid spatial dimension witness")
            if tag == "conv":
                layers.append((tag, channels, filters, kernel, stride, padding, act, bias, side))
                params += filters * (channels * kernel * kernel + int(bias))
                channels = filters
            else:
                layers.append((tag, kind, kernel, stride, padding, side))
            side = out
            features += 1
        elif tag == "flatten":
            if phase != 0 or not features:
                raise ValueError("Flatten needs a nonempty feature stack")
            phase, width = 1, side * side * channels
            layers.append((tag,))
        elif tag == "dense":
            _, units, act, bias = args
            if phase != 1 or hidden >= 2 or type(bias) is not bool:
                raise ValueError("Invalid classification block")
            _int(units, 128, 2048)
            _int(act, 0, 2)
            layers.append((tag, width, units, act, bias))
            params += units * (width + int(bias))
            width = units
            hidden += 1
        elif tag == "softmax":
            if phase != 1 or not hidden:
                raise ValueError("Ten-class head needs a classification block")
            layers.append((tag, width))
            params += 10 * (width + 1)
            phase = 2
        elif tag in {"sgd", "adam", "rmsprop"}:
            if phase != 2:
                raise ValueError("Learner needs a complete classifier")
            _float(args[1], 0.0001, 0.1)
            if tag == "sgd":
                _float(args[2], 0.68, 0.99)
                _float(args[3], 0.000001, 0.001)
                if type(args[4]) is not bool:
                    raise ValueError("Expected Boolean nesterov")
            elif tag == "adam":
                _float(args[2], 0.5, 1.0, exclusive=True)
                _float(args[3], 0.5, 1.0, exclusive=True)
                _float(args[4], 0.000001, 0.001)
            else:
                _float(args[2], 0.5, 1.0, exclusive=True)
                _float(args[3], 0.000001, 0.001)
            _int(args[-2], 5, 20)
            _int(args[-1], 50, 500)
            learning = (tag, *args[1:])
            phase = 3
        else:
            raise ValueError("Unexpected input inside architecture")
    if phase != 3:
        raise ValueError("Incomplete experiment")
    return Encoding(dataset, tuple(layers), learning, params)


def parameter_count(candidate: Any) -> int:
    return decode(candidate).parameters


def build_model(encoding: Encoding):
    """Compile the already-checked Aeon architecture to CPU tensors."""
    from torch import nn
    from torch.nn import functional as F

    class SamePad(nn.Module):
        def __init__(self, kernel: int, stride: int, pool: bool):
            super().__init__()
            self.kernel, self.stride, self.pool = kernel, stride, pool

        def forward(self, x):
            h, w = x.shape[-2:]
            ph = max(0, ((h + self.stride - 1) // self.stride - 1) * self.stride + self.kernel - h)
            pw = max(0, ((w + self.stride - 1) // self.stride - 1) * self.stride + self.kernel - w)
            return F.pad(x, (pw // 2, pw - pw // 2, ph // 2, ph - ph // 2), value=-math.inf if self.pool else 0)

    modules = []
    acts = (nn.Tanh, nn.ReLU, nn.Sigmoid)
    for layer in encoding.layers:
        tag = layer[0]
        if tag == "conv":
            _, cin, cout, k, s, padding, act, bias, _ = layer
            if padding:
                modules.append(SamePad(k, s, False))
            modules.extend((nn.Conv2d(cin, cout, k, s, bias=bias), acts[act]()))
        elif tag == "pool":
            _, kind, k, s, padding, _ = layer
            if padding:
                modules.append(SamePad(k, s, bool(kind)))
            modules.append(nn.MaxPool2d(k, s) if kind else nn.AvgPool2d(k, s))
        elif tag == "flatten":
            modules.append(nn.Flatten())
        elif tag == "dense":
            _, nin, nout, act, bias = layer
            modules.extend((nn.Linear(nin, nout, bias=bias), acts[act]()))
        else:
            modules.extend((nn.Linear(layer[1], 10), nn.Softmax(dim=1)))
    model = nn.Sequential(*modules)
    assert sum(p.numel() for p in model.parameters()) == encoding.parameters
    return model


def optimizer(model, learning: tuple):
    from torch import optim

    tag = learning[0]
    if tag == "sgd":
        _, lr, momentum, decay, nesterov, _, _ = learning
        return optim.SGD(model.parameters(), lr=lr, momentum=momentum, weight_decay=decay, nesterov=nesterov)
    if tag == "adam":
        _, lr, b1, b2, decay, _, _ = learning
        return optim.Adam(model.parameters(), lr=lr, betas=(b1, b2), weight_decay=decay)
    _, lr, rho, decay, _, _ = learning
    return optim.RMSprop(model.parameters(), lr=lr, alpha=rho, weight_decay=decay)


def load_data(path: Path, dataset: int):
    """No test split is accepted by the fitness API. Arrays must be NCHW float32."""
    expected = (1, 28, 28) if dataset == 0 else (3, 32, 32)
    with np.load(path, allow_pickle=False) as archive:
        if set(archive.files) != {"X_train", "y_train", "X_valid", "y_valid"}:
            raise ValueError("NPZ must contain only X_train, y_train, X_valid, y_valid")
        values = tuple(archive[key] for key in ("X_train", "y_train", "X_valid", "y_valid"))
    for x, y in (values[:2], values[2:]):
        if x.dtype != np.float32 or x.shape[1:] != expected or not len(x) or not np.isfinite(x).all():
            raise ValueError("Expected finite, nonempty float32 NCHW images")
        if y.dtype != np.int64 or y.shape != (len(x),) or np.any(y < 0) or np.any(y >= 10):
            raise ValueError("Expected one int64 label in [0,9] per image")
    return values


@contextmanager
def _single_thread():
    import torch

    previous = torch.get_num_threads()
    torch.set_num_threads(1)
    try:
        yield
    finally:
        torch.set_num_threads(previous)


def train_and_score(
    candidate: Any, data: Path, *, epochs: int = 1, seed: int = 42, max_parameters: int = 20_000_000
) -> float:
    """Real held-out accuracy, with fixed initialization/order and early stopping.

    Epoch cap is an evaluation profile, not an evolved grammar production.
    Grammar's published maximum is 400; the default is a one-epoch pilot.
    """
    import torch
    from torch.nn import functional as F

    _int(epochs, 1, 400)
    _int(max_parameters, 1, 1_000_000_000)
    encoding = decode(candidate)
    if encoding.parameters > max_parameters:
        raise ValueError("Candidate exceeds the configured evaluation parameter cap")
    arrays = load_data(data, encoding.dataset)
    with _single_thread(), torch.random.fork_rng(devices=[]):
        torch.manual_seed(seed)
        model = build_model(encoding)
        opt = optimizer(model, encoding.learning)
        xt, yt, xv, yv = (torch.from_numpy(a) for a in arrays)
        patience, batch = encoding.learning[-2:]
        best, stale = -1.0, 0
        for _ in range(epochs):
            model.train()
            order = torch.randperm(len(xt))
            for start in range(0, len(xt), batch):
                indices = order[start : start + batch]
                opt.zero_grad()
                probabilities = model(xt[indices])
                loss = F.nll_loss(probabilities.clamp_min(1e-12).log(), yt[indices])
                if not torch.isfinite(loss):
                    raise ValueError("Nonfinite training loss")
                loss.backward()
                opt.step()
            model.eval()
            correct = 0
            with torch.no_grad():
                for start in range(0, len(xv), batch):
                    scores = model(xv[start : start + batch])
                    if not torch.isfinite(scores).all():
                        raise ValueError("Nonfinite validation scores")
                    correct += int((scores.argmax(1) == yv[start : start + batch]).sum())
            score = correct / len(xv)
            if score > best:
                best, stale = score, 0
            else:
                stale += 1
            if stale >= patience:
                break
    return best


def accuracy(candidate: Any) -> float:
    path = os.environ.get("DENSER_DATA")
    if not path:
        raise ValueError("Set DENSER_DATA to a train/validation NPZ; there is no synthetic fitness fallback")
    return train_and_score(candidate, Path(path), epochs=int(os.environ.get("DENSER_EPOCHS", "1")))


def _allowed(expression, *, smoke: bool = False) -> bool:
    if isinstance(expression, SLiteral):
        return type(expression.value) in (bool, int, float) and (
            type(expression.value) is not float or math.isfinite(expression.value)
        )
    if smoke:
        return False
    if isinstance(expression, SQualifiedVar):
        return expression.qualifier == "Denser" and expression.name.name in CONSTRUCTORS
    if isinstance(expression, SVar):
        return expression.name.name in {f"Denser_{name}" for name in CONSTRUCTORS}
    return isinstance(expression, SApplication) and _allowed(expression.fun) and _allowed(expression.arg)


class DenserBenchmark:
    """Ordinary Aeon search + compiler validation; direct fitness for slow training.

    Bypasses the generic ~1s fitness worker timeout, not the refinement checker.
    Only constructors/literals are admitted; native bodies, recursors, arbitrary
    self calls and accuracy helpers cannot be selected to game the objectives.
    """

    def __init__(self, task: str = "mnist"):
        if task not in {"mnist", "cifar10", "smoke"}:
            raise ValueError("Unknown DENSER task")
        self.task = task
        self.path = TASK_DIR / f"{task}.ae"
        self.source = self.path.read_text()
        driver = self._driver()
        errors = self._parse(driver, self.source)
        if any(not isinstance(e, LiquidTypeCheckingFailedRelation) for e in errors):
            raise ValueError(f"Invalid task: {errors}")
        if driver.core is None or driver.typing_ctx is None:
            raise ValueError("Task did not reach core generation")
        targets = incomplete_functions_and_holes(driver.typing_ctx, driver.core)
        if len(targets) != 1 or len(targets[0][1]) != 1:
            raise ValueError("Expected a single architecture hole")
        self.function, names = targets[0]
        self.goal, ctx = get_holes_info(driver.typing_ctx, driver.core, top, targets, refined_types=True)[names[0]]
        allowed = {f"Denser_{name}" for name in CONSTRUCTORS} if task != "smoke" else set()
        measures = {f"Denser_{m}" for m in ("phase", "dataset", "side", "channels", "features", "hidden")}
        entries = [
            e
            for e in ctx.entries
            if not isinstance(e, (VariableBinder, UninterpretedBinder, ReflectedBinder))
            or e.name.name in allowed
            or (task != "smoke" and isinstance(e, UninterpretedBinder) and e.name.name in measures)
        ]
        self.ctx = dataclasses.replace(ctx, entries=entries)
        self.metadata = {
            self.function: {"goals": [Goal(False, 1, Name("accuracy")), Goal(True, 1, Name("parameters"))]}
        }

    @staticmethod
    def _driver():
        return AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, no_main=True, strict_decidable=True))

    def _parse(self, driver, source):
        return list(driver.parse(filename=str(self.path), aeon_code=source))

    def completed_source(self, candidate: str) -> str:
        # Lifted core terms use canonical internal names; expose the public names.
        for name in CONSTRUCTORS:
            candidate = candidate.replace(f"Denser_{name}", f"Denser.{name}")
        tail = "make_experiment activation" if self.task == "smoke" else "experiment"
        return self.source.replace("?architecture", f"({candidate})") + f"\ndef result : Denser := {tail};\n"

    def verify(self, candidate: str) -> bool:
        try:
            if not _allowed(parse_expression(candidate), smoke=self.task == "smoke"):
                return False
            driver = self._driver()
            errors = self._parse(driver, self.completed_source(candidate))
            return not errors and not driver.has_synth()
        except (ValueError, TypeError, UnexpectedInput):
            return False

    def value(self, candidate: str):
        if not self.verify(candidate):
            raise ValueError("Candidate does not satisfy the Aeon specification")
        # Do not run fitness bindings merely to obtain the architecture.
        source = "\n".join(
            line
            for line in self.completed_source(candidate).splitlines()
            if not line.startswith(("@maximize_float", "@minimize_int"))
        )
        driver = self._driver()
        errors = self._parse(driver, source)
        if errors:
            raise ValueError(errors)
        from aeon.backend.evaluator import eval as evaluate
        from aeon.synthesis.fitness_eval import set_program_tail

        binding = driver.core
        while isinstance(binding, (Let, Rec)):
            if binding.var_name.name == "result":
                return evaluate(set_program_tail(driver.core, Var(binding.var_name)), driver.evaluation_ctx)
            binding = binding.body
        raise ValueError("Compiled result binding is missing")

    def synthesize(self, data: Path, *, backend: str = "enumerative", budget: float = 10, epochs: int = 1):
        if not math.isfinite(budget) or budget <= 0:
            raise ValueError("Budget must be finite and positive")
        _int(epochs, 1, 400)
        load_data(data, 1 if self.task == "cifar10" else 0)
        search = make_synthesizer(backend)
        if not isinstance(search, Synthesizer):
            raise ValueError("Expected a per-hole synthesis backend")
        cache: dict[str, tuple[float, int]] = {}

        def text(term: Term) -> str:
            return pretty_print_sterm(lift(term), top_level=False)

        def fitness(term: Term) -> list[float]:
            candidate = text(term)
            try:
                if candidate not in cache:
                    value = self.value(candidate)
                    cache[candidate] = (train_and_score(value, data, epochs=epochs), parameter_count(value))
            except ValueError as error:
                raise InvalidIndividualException() from error
            return list(cache[candidate])

        try:
            term = search.synthesize(
                self.ctx,
                self.goal,
                lambda t: self.verify(text(t)),
                fitness,
                self.function,
                self.metadata,
                budget,
                SilentSynthesisUI(),
            )
        except SynthesisNotSuccessful:
            return None
        if term is None or not self.verify(text(term)):
            return None
        candidate = text(term)
        score = fitness(term)
        return {
            "candidate": candidate,
            "validation_accuracy": score[0],
            "parameters": int(score[1]),
            "epochs_cap": epochs,
            "source_commit": SOURCE_COMMIT,
        }


def prepare(dataset: str, root: Path, output: Path, *, download: bool = False) -> None:
    """Prepare official training examples with the reference split sizes."""
    import torch
    from torchvision import datasets, transforms

    if dataset not in {"mnist", "cifar10"}:
        raise ValueError("Expected MNIST or CIFAR-10")
    if output.suffix != ".npz":
        raise ValueError("Output must have a .npz extension")
    if output.exists():
        raise FileExistsError(output)
    transform = transforms.Compose([transforms.ToTensor(), transforms.Normalize((0.1307,), (0.3081,))])
    cls = datasets.MNIST if dataset == "mnist" else datasets.CIFAR10
    images = cls(str(root), train=True, download=download, transform=transform)
    ntrain = 50_000 if dataset == "mnist" else 40_000
    if len(images) != ntrain + 10_000:
        raise ValueError("Unexpected official training dataset size")
    order = torch.randperm(len(images), generator=torch.Generator().manual_seed(42)).tolist()
    shape = (1, 28, 28) if dataset == "mnist" else (3, 32, 32)
    x = np.empty((len(images), *shape), dtype=np.float32)
    y = np.empty(len(images), dtype=np.int64)
    for index, original in enumerate(order):
        image, label = images[original]
        x[index], y[index] = image.numpy(), label
    np.savez_compressed(output, X_train=x[:ntrain], y_train=y[:ntrain], X_valid=x[ntrain:], y_valid=y[ntrain:])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--task", choices=("mnist", "cifar10", "smoke"), default="mnist")
    parser.add_argument("--data", type=Path, required=True)
    parser.add_argument("--candidate")
    parser.add_argument("--backend", default="gp")
    parser.add_argument("--budget", type=float, default=60)
    parser.add_argument("--epochs", type=int, default=1)
    parser.add_argument("--prepare", type=Path, metavar="DATASET_ROOT")
    parser.add_argument("--download", action="store_true")
    args = parser.parse_args()
    if args.prepare:
        if args.task == "smoke":
            parser.error("Prepare MNIST or CIFAR-10, not synthetic smoke data")
        prepare(args.task, args.prepare, args.data, download=args.download)
        return 0
    benchmark = DenserBenchmark(args.task)
    if args.candidate is not None:
        value = benchmark.value(args.candidate)
        report = {
            "candidate": args.candidate,
            "validation_accuracy": train_and_score(value, args.data, epochs=args.epochs),
            "parameters": parameter_count(value),
            "epochs_cap": args.epochs,
            "source_commit": SOURCE_COMMIT,
        }
    else:
        report = benchmark.synthesize(args.data, backend=args.backend, budget=args.budget, epochs=args.epochs)
    print(json.dumps(report or {"status": "no_solution"}))
    return 0 if report else 2


if __name__ == "__main__":
    raise SystemExit(main())
