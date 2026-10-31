from time import monotonic
import random

import pytest

from aeon.core.types import t_bool, t_int, t_string
from aeon.synthesis.modules.type_constrained.prefix import Limits, PrefixEngine
from aeon.synthesis.modules.type_constrained.sampling import (
    Decoded,
    DecodingCancelled,
    DecodingExhausted,
    Sampling,
    Statistics,
    decode,
)
from aeon.synthesis.modules.type_constrained.types import Scope
from aeon.typechecking.context import TypingContext
from tests.type_constrained_prefix_test import context


class FakeAdapter:
    eos_ids = frozenset({0})
    special_ids = frozenset({0})

    def __init__(self, pieces, rankings, detokenize=None):
        self.pieces = pieces
        self.rankings = rankings
        self.detokenize = detokenize
        self.ids = []
        self.commits = []
        self.previews = []

    def start(self, prompt):
        self.ids = []

    def scores(self):
        ranking = self.rankings[min(len(self.ids), len(self.rankings) - 1)]
        return [
            float(len(ranking) - ranking.index(i)) if i in ranking else -float("inf") for i in range(len(self.pieces))
        ]

    def preview(self, token):
        self.previews.append((tuple(self.ids), token))
        ids = [*self.ids, token]
        return self.detokenize(ids) if self.detokenize else Decoded("".join(self.pieces[i] for i in ids))

    def commit(self, token):
        self.ids.append(token)
        self.commits.append(token)


def run(adapter, ty=t_bool, settings=Sampling(), stats=None, cancelled=lambda: False, ctx=None):
    return decode(
        adapter,
        PrefixEngine(Scope(ctx if ctx is not None else context(), ty)),
        "prompt",
        monotonic() + 10,
        random.Random(17),
        settings,
        stats,
        cancelled,
    )


def test_invalid_highest_token_and_eos_rejected_before_commit_outside_top_k():
    adapter = FakeAdapter(["<eos>", "f true ", "bad ", "f 0"], [[0, 1, 2, 3], [0]])
    stats = Statistics()
    assert run(adapter, settings=Sampling(initial_top_k=1), stats=stats) == "f 0"
    assert adapter.commits == [3, 0]
    assert adapter.previews[:3] == [((), 1), ((), 2), ((), 3)]
    assert stats.rejected_tokens == 3


def test_multichar_tokens_cross_boundaries_and_incomplete_eos():
    adapter = FakeAdapter(["<eos>", "(f ", "0) && true"], [[1], [0, 2], [0]])
    assert run(adapter) == "(f 0) && true"
    assert adapter.commits == [1, 2, 0]


def test_context_dependent_detokenization_rechecks_whole_sequence():
    def detokenize(ids):
        return Decoded({(1,): "f ", (1, 2): "false"}[tuple(ids)])

    adapter = FakeAdapter(["<eos>", "unused", "unused"], [[1], [2], [0]], detokenize)
    assert run(adapter) == "false"
    assert adapter.commits == [1, 2, 0]


def test_escape_split_and_unicode():
    adapter = FakeAdapter(["<eos>", '"λ\\', 'n"'], [[1], [2], [0]])
    assert run(adapter, t_string) == '"λ\\n"'


def test_unfinished_utf8_is_never_committed():
    def detokenize(ids):
        return Decoded('"\ufffd', stable=False) if ids == [1] else Decoded('"λ"')

    adapter = FakeAdapter(["<eos>", "byte", '"λ"'], [[1, 2], [0]], detokenize)
    stats = Statistics()
    assert run(adapter, t_string, stats=stats) == '"λ"'
    assert adapter.commits == [2, 0] and stats.unknown_tokens == 1


def test_token_and_probe_exhaustion_are_explicit():
    adapter = FakeAdapter(["<eos>", "f "], [[1]])
    with pytest.raises(DecodingExhausted, match="token budget"):
        run(adapter, settings=Sampling(max_tokens=1))
    adapter = FakeAdapter(["<eos>", "bad ", "0"], [[1, 2]])
    with pytest.raises(DecodingExhausted, match="probe bound"):
        run(adapter, t_int, settings=Sampling(max_probes=1))
    assert adapter.commits == []


def test_cancellation_and_expired_deadline_do_not_commit():
    adapter = FakeAdapter(["<eos>", "f ", "0"], [[1], [2]])
    with pytest.raises(DecodingCancelled):
        run(adapter, cancelled=lambda: len(adapter.commits) == 1)
    assert adapter.commits == [1]
    with pytest.raises(DecodingExhausted):
        decode(adapter, PrefixEngine(Scope(context(), t_bool)), "", monotonic() - 1, random.Random(1))
    assert adapter.commits == [1]


def test_seeded_temperature_samples_allowed_distribution():
    outputs = []
    for seed in range(40):
        adapter = FakeAdapter(["<eos>", "true", "false", "bad "], [[3, 1, 2], [0]])
        outputs.append(
            decode(
                adapter,
                PrefixEngine(Scope(TypingContext(), t_bool)),
                "",
                monotonic() + 3,
                random.Random(seed),
                Sampling(temperature=1, initial_top_k=1),
            )
        )
        assert 3 not in adapter.commits
    assert set(outputs) == {"true", "false"}


def test_unknown_oracle_result_is_not_promoted_to_live():
    adapter = FakeAdapter(["<eos>", "true"], [[1]])
    stats = Statistics()
    engine = PrefixEngine(Scope(context(), t_bool), Limits(max_states=1))
    with pytest.raises(DecodingExhausted, match="not a proof"):
        decode(adapter, engine, "", monotonic() + 1, random.Random(0), stats=stats)
    assert adapter.commits == [] and stats.unknown_tokens == 1
