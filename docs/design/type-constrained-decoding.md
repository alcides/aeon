# Type-constrained decoding

`-s llm_type_constrained` implements the completion-oracle approach of
[Mündler et al., PLDI 2025](https://arxiv.org/abs/2504.09246) for a bounded Aeon
fragment. The [author implementation](https://github.com/eth-sri/type-constrained-code-generation)
was consulted (MIT license); no TypeScript parser code is copied or imported.
This is an Aeon implementation, not a reproduction of the paper's evaluation.

## Supported source fragment

One hole, ordinary monomorphic `Int`, `Bool`, `String`, `Float`, `Unit`, and
unrestricted arrows. Components come from the hole's lexical typing context.
Supported syntax includes identifiers (including qualified names already
present in that context), literals, curried application, grouping, primitive
operators, `if ... then ... else ...`, nonrecursive `let x := value in body`
(also `;`), and `fun x => body` with an expected arrow type. Operator precedence
follows `aeon_sugar.lark`; the final compiler determines associativity.

The finite type universe comprises primitive types and arrow subtypes of the
goal/components. It bounds inferred let types and parenthesized function
applications; it does not invent arbitrary intermediate higher-order types.
Integer literals are nonnegative, as in Aeon's surface grammar; use `0 - n`
for a negative integer. Float literals must be finite. Float exponents and unfinished strings/escapes remain
viable when a completion exists. Common Python/Aeon escapes and hexadecimal
`\x`, `\u`, `\U` escapes are supported; named Unicode escapes are excluded.
Comments, annotations on generated binders, operator sections, method dispatch,
type applications, pattern matching, and recursive definitions are outside this
initial grammar. Imported components use the canonical names exposed in the
hole context/prompt; source import aliases unavailable in that context are not
guessed.

Unsupported goal types, polymorphism, abstract-refinement quantifiers, ADTs,
linear/erased binders on the path to a hole, recursion requests, and multiple
program holes produce capability errors. Irrelevant unsupported components are
filtered out. Only built-in operators are monomorphized; arbitrary polymorphic
components are not approximated. Fitness helpers, excluded intrinsics, and the
function being synthesized are hidden. Inner bindings shadow outer ones.

Incremental typing erases concrete refinements. **It does not establish refinement
correctness.** At EOS, the source is parsed, qualified names are resolved, free
names retain their actual `Name` IDs, local binders receive fresh IDs, and Aeon's
elaborator inserts required type applications. This runs under the captured
compilation session. The supplied original validator is then called before
normal example/property/fitness evaluation and Pareto selection.

## Completion oracle

`Scope(context, goal)` fixes the environment and session. `PrefixEngine` exposes
`advance(State, characters)`, `is_accepting`, and `completion_status`. States are
immutable text snapshots. Each probe explores a nondeterministic worklist of
typed grammar continuations: precedence frames, lexical alternatives, scoped
names, and outstanding terminals. It reconstructs the worklist from the snapshot
and caches completed queries; it does not treat failed whole-program parses as
evidence about incomplete prefixes.

The oracle returns:

- `LIVE`: an explicit full source witness extending the prefix.
- `DEAD`: all searched derivations in the documented grammar were exhausted.
- `UNKNOWN`: work, stack, text-size, or wall-clock limits prevented a decision.

Type inhabitation searches introductions and application spines, with cycle
detection keyed by both target type and available environment types. Incomplete
expressions can change type by applying a function or adding an operator. An
integer prefix is therefore retained when it can become a Boolean comparison.
Lexical alternatives are preserved: `f` may be the start of a longer identifier
or keyword, and an unfinished string is not automatically invalid.

Prefix and successful type-derivation caches belong to one engine/scope, are
each bounded to 512 entries, and contain no deadline-dependent `UNKNOWN`
answers or cyclic partial failures. No global name/type cache is
shared between compilation sessions. The worklist is bounded to 128 continuation
frames and source text to 2048 characters. A failed bounded decoding attempt is
reported as resource exhaustion, never as proof that the user's full Aeon type
is uninhabited. Offline differential tests compile/typecheck LIVE witnesses with
Aeon's independent compiler.

## Sampling and adapter

The adapter protocol separates scores, trial detokenization, and commitment.
Trials decode the **whole token sequence**, including prompt context; they do
not concatenate `decode([token])`. Context-dependent changes to generated text
are rechecked from a fresh snapshot. Prompt-boundary rewrites and unfinished
UTF-8 decoding (ambiguous U+FFFD) are conservatively excluded. Complete Unicode
strings are supported; this implementation does not claim complete support for
tokenizers that require committing unfinished byte fragments.

Only certified LIVE transitions are committed. Other special tokens and
zero-progress tokens are excluded. EOS requires a complete accepting expression;
a token-limit stop cannot return a hole or partial program. Top-k controls probe
batches, not the available language: search continues beyond the first batch.
Temperature zero uses the highest-scoring certified token. Positive temperature
uses a seeded Gumbel ranking over the full finite score vector and rejection
sampling, preserving the conditional allowed-token distribution when search
finishes. A probe limit aborts explicitly rather than sampling a truncated
distribution.

The optional adapter uses `AutoTokenizer` and `AutoModelForCausalLM`, with
`trust_remote_code=False` and lazy imports. It performs actual next-token forward
passes. The initial implementation disables KV caching and recomputes logits
from committed IDs, so rejected tokens cannot contaminate model state. This is
a correctness-first adapter, not a throughput optimization. See the official
[Transformers generation API](https://huggingface.co/docs/transformers/en/internal/generation_utils).

## Configuration and time bounds

Install into an activated virtual environment with
`uv pip install -e '.[dev,llm-type-constrained]'`. No model is downloaded by
default tests. Set `AEON_TC_MODEL` explicitly; a local directory also works
offline. A remote model ID invokes the normal Hugging Face download behavior.

| Variable | Default | Meaning |
| --- | --- | --- |
| `AEON_TC_PROVIDER` | `transformers` | Other providers raise a capability error |
| `AEON_TC_MODEL` | required | Local model path or Hugging Face model ID |
| `AEON_TC_DEVICE` | `cpu` | Torch device, e.g. `cuda` or `mps` |
| `AEON_SEED` | `0` | Local sampling and Pareto-selection seed |
| `AEON_TC_TEMPERATURE` | `0` | Greedy or positive-temperature sampling |
| `AEON_TC_MAX_TOKENS` | `128` | Tokens per attempt, including EOS |
| `AEON_TC_MAX_PROBES` | `4096` | Candidate token probes per decoding step |
| `AEON_TC_TOP_K` | `32` | Initial/continued probe batch size |
| `AEON_TC_MAX_STATES` | `20000` | Grammar/inhabitation work per prefix query |
| `AEON_TC_ATTEMPTS` | `8` | Maximum attempts, including refinement retries |

One monotonic deadline covers model loading, token probes, completion search,
retries, final validation, and evaluation. It is checked before and after model
calls and synchronous compiler/evaluator work. An in-flight model load/forward,
compiler call, or evaluator cannot be preempted by this adapter; late results
are rejected. Prefix work checks the deadline during search. The standalone
sampler also accepts a cancellation callback, checked between bounded probes.
Model initialization is included in the synthesis budget; pre-cache large
models and select a suitable budget. There is no silent provider fallback.

## Examples and evidence

The ordinary `.ae` files in `examples/synthesis/type_constrained/` cover
application, a conditional with let binding, a whole function hole, and a
positive refinement that must reject zero. They also work with compatible
existing backends. `@prompt` and source examples are included in the model
prompt; normal shared evaluators supply objective values.

```bash
python -m pytest tests/type_constrained_prefix_test.py \
  tests/type_constrained_sampling_test.py tests/type_constrained_synthesizer_test.py

# Real neural forward passes through the adapter, no downloads (requires Torch):
python -m aeon.synthesis.modules.type_constrained.smoke --report /tmp/tc-torch.json

# Actual local GPT-2 + fast-tokenizer save/load/forward path, also no downloads:
python -m aeon.synthesis.modules.type_constrained.smoke --transformers \
  --report /tmp/tc-transformers.json
python -m pytest tests/type_constrained_integration_test.py
```

The fixtures deliberately make an invalid token rank highest. They run actual
neural forward passes, then require masking to find a lower-ranked token and
legal EOS. Reports record tokens, rejected/unknown tokens, oracle time, and
independent final validation. The GRU has fixed output biases; the tiny GPT-2
has zero weights. These fixtures test the adapter, **not trained-model generation
quality**, performance rankings, or the paper's reported outcomes. No comparison
against unconstrained or syntax-only generation is claimed. Optional integration
tests skip when their dependencies are absent. Per-run backend counters are also
available as `TypeConstrainedSynthesizer.statistics`.

The checked-in [Torch smoke report](type-constrained-smoke.json) and
[Transformers smoke report](type-constrained-transformers-smoke.json) each record
three independently validated cases, with two committed tokens (including EOS)
and five rejected token trials per case. Both optional integration tests passed
using Torch 2.14.1 CPU and Transformers 5.22.1. The Transformers run exercised
actual local GPT-2 and fast-tokenizer save/load and forward passes. No pretrained
model evaluation is included in this change.
