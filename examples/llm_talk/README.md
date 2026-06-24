# Programming Languages in the LLM World — a worked sequence

An eight-step arc on refinement types: what they are, where they stop, how they
look in real domains, and why they are the right substrate for trustworthy
LLM-generated code. Each `.ae` file runs on its own; the comments inside carry
the talking points.

Run any example:

```bash
uv run python -m aeon examples/llm_talk/<file>.ae
```

| # | File | Beat | What to show live |
|---|------|------|-------------------|
| 1 | `1_types_are_not_enough.ae` | **Problem.** Ordinary types are too coarse. | Runs, prints `2` — a *wrong* `max`, fully well-typed. The bug an LLM ships. |
| 2 | `2_refinements.ae` | **Idea.** `{x:Base \| pred}` puts logic in the type. | Runs (`5.0`). Aeon refines `/` for free; edit the call to `average 10 0` → compile-time rejection, no test run. |
| 3 | `3_specs_as_types.ae` | **Power.** A return refinement is a machine-checked spec. | `abs` and a *proof* that a ReLU layer is monotone — verification, not a test suite. |
| 4 | `4_limitations.ae` | **Limits.** A refinement only checks what you wrote. | A weak spec rubber-stamps the buggy `max` from step 1; uncomment the strong spec → rejected. Plus: the logic is a decidable fragment. |
| 5 | `5_robotics_rospec.ae` | **In the wild: robotics.** Refinements as a robot-safety contract. | Non-negative joint accel, velocity clamp, collision-avoidance precondition, and the ROSpec Fig. 1 grayscale-vs-RGB bug — `connect_image 3 1` is a type error. |
| 6 | `6_ml_pipeline.ae` | **In the wild: ML.** Refinements as data contracts. | Min-max normalization proven in [0,1], probabilities that stay probabilities, a bounded learning rate, and a no-leakage train/test split (`test_size 100 100` rejected). |
| 7 | `7_synthesis.ae` | **Flip.** If the type is the spec, search writes the body. | `?hole` filled to `105`, `?body` filled to `i + i`, from the types alone. |
| 8 | `8_llm_plus_refinements.ae` | **Thesis.** LLM proposes, refinement type disposes. | `@prompt` + a refinement: the LLM is the generator, the type checker is the gate. |

Steps 5 and 6 are the "this is not a toy" interlude: the same `{x | pred}`
machinery, now expressing real robot-safety and ML-pipeline invariants, right
before the talk flips from *checking* to *generating*.

## The robotics step (5)

Adapted from **ROSpec** — *A Domain-Specific Language for ROS-Based Robot
Software*, Canelas, Schmerl, Fonseca & Timperley, OOPSLA 2025
([10.1145/3763169](https://doi.org/10.1145/3763169)) — which puts liquid types
on ROS component configurations. The paper's motivating misconfiguration (Fig.
1) is a publisher sending RGB images to a subscriber that expects grayscale;
step 5 reconstructs that bug as a type error, alongside the paper's
`max_acceleration where {_ >= 0}` parameter bound.

## The synthesis steps (7 & 8)

```bash
# Type-driven synthesis — deterministic, SMT-backed. Fills the holes with 105 and i+i.
uv run python -m aeon -s synquid examples/llm_talk/7_synthesis.ae

# LLM-driven synthesis — needs a local ollama model (qwen2.5:32b). The refinement
# is the contract every LLM candidate must pass before it is accepted.
uv run python -m aeon -s llm examples/llm_talk/8_llm_plus_refinements.ae
```

## The one-slide takeaway

```
refinements   = a machine-checkable contract  (the "what")
verification  = reject wrong code, including the LLM's   (soundness)
synthesis     = let a proposer — search OR an LLM — fill the hole
```

The architecture is in `aeon/synthesis/modules/llm/__init__.py:93`:

```python
if validate(core_tterm):     # every LLM candidate runs through the SAME
    ...return it...          # refinement-type checker from steps 2–6
else:
    ...reject, ask again...  # hallucinations filtered structurally
```

The LLM never gets the last word. Generation gets the model's speed and
breadth; correctness gets the type system's guarantees. In the LLM world,
types stop being documentation and become the interface between what we can
say we want and what a stochastic model gives us.
