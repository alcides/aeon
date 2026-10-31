"""Reproducible neural-inference smoke, with no model download or service.

This is a deterministic masking fixture, not a trained-model quality benchmark.
The default runs a tiny Torch GRU through the real adapter; --transformers also
exercises save/load and inference with an actual Transformers GPT-2 model and
fast tokenizer. Imports remain optional and local to the fixture functions.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict
from importlib.metadata import version
import json
from pathlib import Path
import random
import tempfile
from time import monotonic
from types import SimpleNamespace
from typing import Any

from aeon.core.types import AbstractionType, t_bool, t_int
from aeon.synthesis.modules.type_constrained.prefix import PrefixEngine
from aeon.synthesis.modules.type_constrained.sampling import Sampling, Statistics, decode
from aeon.synthesis.modules.type_constrained.transformers_adapter import TransformersAdapter
from aeon.synthesis.modules.type_constrained.types import Scope
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name


def _fixture(expression: str, directory: Path, transformers: bool) -> TransformersAdapter:
    import torch

    vocabulary = ["<eos>", "<unk>", "Prompt", expression, "not_in_scope"]
    if transformers:
        from tokenizers import Tokenizer
        from tokenizers.models import WordLevel
        from tokenizers.pre_tokenizers import WhitespaceSplit
        from transformers import GPT2Config, GPT2LMHeadModel, PreTrainedTokenizerFast

        tokenizer = Tokenizer(WordLevel(dict(zip(vocabulary, range(len(vocabulary)))), unk_token="<unk>"))
        tokenizer.pre_tokenizer = WhitespaceSplit()
        fast = PreTrainedTokenizerFast(tokenizer_object=tokenizer, eos_token="<eos>", unk_token="<unk>")
        with torch.random.fork_rng():
            torch.manual_seed(0)
            model = GPT2LMHeadModel(
                GPT2Config(vocab_size=5, n_positions=64, n_embd=8, n_layer=1, n_head=1, bos_token_id=2, eos_token_id=0)
            )
            for parameter in model.parameters():
                parameter.data.zero_()
        model.save_pretrained(directory)
        fast.save_pretrained(directory)
        return TransformersAdapter.load(str(directory))

    class VocabularyTokenizer:
        eos_token_id = 0
        bos_token_id = 2
        all_special_ids = [0, 1]

        def encode(self, text, add_special_tokens=True):
            return [vocabulary.index(word) if word in vocabulary else 1 for word in text.split()]

        def decode(self, ids, **kwargs):
            return " ".join(vocabulary[token] for token in ids)

    class TinyCausalModel(torch.nn.Module):
        def __init__(self):
            super().__init__()
            self.embedding = torch.nn.Embedding(5, 8)
            self.rnn = torch.nn.GRU(8, 8, batch_first=True)
            self.head = torch.nn.Linear(8, 5)
            self.config = SimpleNamespace(max_position_embeddings=64)
            self.forward_calls = 0
            # Fixed output biases make the invalid token highest on every
            # real neural forward pass. The oracle must reject it before commit.
            self.head.weight.data.zero_()
            self.head.bias.data.copy_(torch.arange(5, dtype=torch.float))

        @property
        def device(self):
            return self.embedding.weight.device

        def forward(self, input_ids, use_cache=False):
            self.forward_calls += 1
            hidden, _ = self.rnn(self.embedding(input_ids))
            return SimpleNamespace(logits=self.head(hidden))

    with torch.random.fork_rng():
        torch.manual_seed(0)
        model = TinyCausalModel()
    return TransformersAdapter(model, VocabularyTokenizer())


def run_smoke(*, transformers: bool = False) -> dict[str, Any]:
    import torch

    cases = [
        ("literal", "true", TypingContext(), t_bool),
        (
            "application",
            "f 0",
            TypingContext().with_var(Name("f", 40001), AbstractionType(Name("x", 40002), t_int, t_bool)),
            t_bool,
        ),
        ("function", "fun x => x", TypingContext(), AbstractionType(Name("x", 40003), t_int, t_int)),
    ]
    records = []
    with tempfile.TemporaryDirectory(prefix="aeon-type-constrained-smoke-") as directory:
        for name, expression, context, expected in cases:
            adapter = _fixture(expression, Path(directory) / name, transformers)
            engine = PrefixEngine(Scope(context, expected))
            stats = Statistics()
            start = monotonic()
            source = decode(adapter, engine, "Prompt", start + 30, random.Random(0), Sampling(max_tokens=4), stats)
            term = engine.scope.compile(source)
            valid = check_type(context, term, expected)
            assert valid and stats.rejected_tokens > 0
            stats.attempts = 1
            stats.validation_passed = int(valid)
            records.append(
                {"case": name, "source": source, "validated": valid, "seconds": monotonic() - start, **asdict(stats)}
            )
    return {
        "fixture": "Transformers GPT-2 (zero weights)" if transformers else "Torch GRU (fixed output biases)",
        "torch_version": torch.__version__,
        **({"transformers_version": version("transformers")} if transformers else {}),
        "seed": 0,
        "temperature": 0,
        "max_tokens": 4,
        "purpose": "adapter/masking correctness, not generation quality",
        "cases": records,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--transformers", action="store_true")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    report = json.dumps(run_smoke(transformers=args.transformers), indent=2) + "\n"
    if args.report:
        args.report.write_text(report)
    print(report, end="")


if __name__ == "__main__":
    main()
