"""Optional real local inference. Importing this file does not import Torch.

The initial adapter recomputes logits from committed IDs, with caching disabled:
there is no speculative KV state to roll back. Full-context detokenization is
used for every trial. A tokenizer that rewrites the prompt boundary or emits an
unfinished UTF-8 sequence is conservatively unavailable for that transition.
"""

from __future__ import annotations

from typing import Any

from aeon.synthesis.api import UnsupportedSynthesisGoal
from aeon.synthesis.modules.type_constrained.sampling import Decoded, DecodingExhausted


class TransformersAdapter:
    def __init__(self, model: Any, tokenizer: Any):
        self.model = model.eval()
        self.tokenizer = tokenizer
        eos = tokenizer.eos_token_id
        if eos is None:
            raise UnsupportedSynthesisGoal("the local tokenizer must define an EOS token")
        self.eos_ids = frozenset([eos] if isinstance(eos, int) else eos)
        self.special_ids = frozenset(tokenizer.all_special_ids)
        self.ids: list[int] = []
        self.prompt_text = ""

    @classmethod
    def load(cls, model_name: str, device: str = "cpu") -> TransformersAdapter:
        try:
            from transformers import AutoModelForCausalLM, AutoTokenizer
            import torch  # noqa: F401
        except ImportError as error:
            raise UnsupportedSynthesisGoal(
                "install AeonLang[llm-type-constrained] for local Transformers inference"
            ) from error
        tokenizer = AutoTokenizer.from_pretrained(model_name, trust_remote_code=False)
        model = AutoModelForCausalLM.from_pretrained(model_name, trust_remote_code=False).to(device)
        return cls(model, tokenizer)

    def _decode(self, ids: list[int]) -> str:
        return self.tokenizer.decode(ids, skip_special_tokens=False, clean_up_tokenization_spaces=False)

    def start(self, prompt: str) -> None:
        self.ids = list(self.tokenizer.encode(prompt, add_special_tokens=True))
        if not self.ids:
            bos = self.tokenizer.bos_token_id
            if bos is None:
                raise UnsupportedSynthesisGoal("empty prompt requires a tokenizer BOS token")
            self.ids = [bos]
        self.prompt_text = self._decode(self.ids)

    def scores(self) -> list[float]:
        import torch

        limit = getattr(self.model.config, "max_position_embeddings", None)
        if limit and len(self.ids) >= limit:
            raise DecodingExhausted("local model context window exhausted")
        with torch.inference_mode():
            inputs = torch.tensor([self.ids], dtype=torch.long, device=self.model.device)
            result = self.model(input_ids=inputs, use_cache=False)
            return result.logits[0, -1].float().cpu().tolist()

    def preview(self, token: int) -> Decoded:
        try:
            text = self._decode([*self.ids, token])
        except (IndexError, KeyError, ValueError, OverflowError):
            # Some causal models pad their output vocabulary beyond the
            # tokenizer's IDs. Such scores do not denote text transitions.
            return Decoded("", stable=False)
        if not text.startswith(self.prompt_text):
            return Decoded("", stable=False)
        generated = text[len(self.prompt_text) :]
        # U+FFFD is ambiguous with byte-fallback decoding's unfinished output.
        # Reject conservatively (including a genuine replacement character).
        return Decoded(generated, stable="\ufffd" not in generated)

    def commit(self, token: int) -> None:
        self.ids.append(token)
