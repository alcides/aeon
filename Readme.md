# Aeon

Aeon is a statically-typed programming language with native support for **Liquid Types** (refinement types), developed at [LASIGE](https://www.lasige.pt), University of Lisbon.

Unlike [LiquidHaskell](https://ucsd-progsys.github.io/liquidhaskell/) or [LiquidJava](https://catarinagamboa.github.io/liquidjava.html), where refinement types are bolted onto an existing language, Aeon was designed from the ground up around them. The type system lets you express precise properties of values directly in types — for example, "an integer greater than zero" — and the compiler proves these properties hold using the [Z3 SMT solver](https://github.com/Z3Prover/z3).

Beyond refinement types, Aeon also offers:

- **Python FFI** — call any Python function natively, giving you access to the full Python ecosystem.
- **Program synthesis** — leave `?hole`s in your program and let Aeon fill them in using genetic programming, enumerative search, or LLM-backed synthesis.
- **A growing standard library** — modules for `List`, `Math`, `Array`, `Image`, and more.

Aeon is implemented as a Python interpreter and is under active development.

📖 **Documentation:** [https://alcides.github.io/aeon](https://alcides.github.io/aeon)

## Installation

Aeon is distributed on PyPI and can be run directly via [uvx](https://github.com/astral-sh/uv):

```bash
uvx --from aeonlang aeon [file.ae]
```

## Examples

### Refinement Types

Refinement types let you attach predicates to base types. Here, `sqrt` is declared to accept only positive integers — passing a negative value is a *compile-time* error, not a runtime crash. The `native` keyword bridges to Python:

```aeon
def sqrt : (i: {x:Int | x > 0}) -> Float := native "__import__('math').sqrt";

def main (i:Int) : Unit :=
    print (sqrt (-25))   # type-checking error: -25 does not satisfy x > 0
```

### Program Synthesis

Aeon can synthesize code to satisfy a refinement specification. Mark the body with `?hole` and Aeon will search for an implementation that meets the type:

```aeon
@minimize_int(deposit)
def deposit : {d:Int | d > 0 && d * 21900 >= 10000000} := ?hole;
```

Run with `uv run python -m aeon --budget 10 -s gp file.ae` to synthesize the minimum annual deposit that reaches a $10,000 goal in 20 years at 1% interest.

More examples — including image processing, machine learning, and probabilistic programming — live in the [`examples/`](examples/) directory.

## Authors

Aeon has been developed at [LASIGE](https://www.lasige.pt), [University of Lisbon](https://ciencias.ulisboa.pt) by:

* [Alcides Fonseca](http://alcidesfonseca.com)
* [Paulo Santos](https://pcanelas.com/)
* [Eduardo Madeira](https://www.lasige.pt/member/jose-eduardo-madeira)
* [Guilherme Espada](https://espada.dev)
* [Lishun Su](https://lasige.pt/member/su-lishun/)
* [Paulo Silva](https://github.com/PauloHS-Silva)
* [Diogo Sousa](https://github.com/SousaTrashBin)

## Publications

* [Comparing the expressive power of Strongly-Typed and Grammar-Guided Genetic Programming](https://www.researchgate.net/publication/370277603_Comparing_the_expressive_power_of_Strongly-Typed_and_Grammar-Guided_Genetic_Programming) at GECCO'23
* [The Usability Argument for Refinement Typed Genetic Programming](https://link.springer.com/chapter/10.1007/978-3-030-58115-2_2) at PPSN'20

Let us know if your paper uses Aeon, to list it here.

### Citation

Please cite as:

```
Fonseca, Alcides, Paulo Santos, and Sara Silva. "The usability argument for refinement typed genetic programming." International Conference on Parallel Problem Solving from Nature. Cham: Springer International Publishing, 2020.
```

BibTeX:

```bibtex
@inproceedings{fonseca2020usability,
  title={The usability argument for refinement typed genetic programming},
  author={Fonseca, Alcides and Santos, Paulo and Silva, Sara},
  booktitle={International Conference on Parallel Problem Solving from Nature},
  pages={18--32},
  year={2020},
  organization={Springer}
}
```

## Acknowledgements

This work was supported by Fundação para a Ciência e Tecnologia (FCT) through:

* [the LASIGE Research Unit](https://www.lasige.pt) (ref. UID/00408/2025)
* [the FCT Exploratory project RAP](http://wiki.alcidesfonseca.com/research/projects/rap/) (EXPL/CCI-COM/1306/2021)
* the FCT Advanced Computing projects (CPCA/A1/395424/2021, CPCA/A1/5613/2020, CPCA/A2/6009/2020)

And by Lisboa2020, Compete2020 and FEDER through:

* [the CMU|Portugal CAMELOT project](http://wiki.alcidesfonseca.com/research/projects/camelot/) (LISBOA-01-0247-FEDER-045915)
