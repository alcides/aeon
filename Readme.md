# Aeon 4

Aeon is a programming languages that features Liquid Types, developed at the University of Lisbon. Unlike [LiquidHaskell](https://ucsd-progsys.github.io/liquidhaskell/) or [LiquidJava](https://catarinagamboa.github.io/liquidjava.html), Aeon was designed from the ground up to have support for Liquid Types.

Aeon is in development, so assume all your programs to break. This 4th version is implemented as a Python interpreter, giving you access to any code written in Python.

## Examples


### Hello World

```
def main (args:Int) : Unit {
    print "Hello World"
}
```

The documentation is available at [https://alcides.github.io/aeon](https://alcides.github.io/aeon).


### Liquid Types

In this example, you can see the refined type `{x:Int | x > 0}` that represents all integers that are greater than 0. You can also see an example of Python FFI, where a python valid expression can be written as string and passed as the argument to the `native` function.

```
def sqrt : (i: {x:Int | x > 0} ) -> Float = native "__import__('math').sqrt";

def main (i:Int) : Unit {
    print (sqrt (-25)) # This is a type-checking error!
}
```



Authors
----------
Aeon has been developed at [LASIGE](https://www.lasige.pt), [University of Lisbon](https://ciencias.ulisboa.pt) by:

* [Alcides Fonseca](http://alcidesfonseca.com)
* [Paulo Santos](https://pcanelas.com/)
* [Eduardo Madeira](https://www.lasige.pt/member/jose-eduardo-madeira)
* [Guilherme Espada](https://espada.dev)
* [Lishun Su](https://lasige.pt/member/su-lishun/)
* [Paulo Silva](https://github.com/PauloHS-Silva)
* [Diogo Sousa](https://github.com/SousaTrashBin)

Acknowledgements
----------------

This work was supported by Fundação para a Ciência e Tecnologia (FCT) through:

* [the LASIGE Research Unit](https://www.lasige.pt) (ref. UID/00408/2025)
* [the FCT Exploratory project RAP](http://wiki.alcidesfonseca.com/research/projects/rap/) (EXPL/CCI-COM/1306/2021)
* the FCT Advanced Computing projects (CPCA/A1/395424/2021, CPCA/A1/5613/2020, CPCA/A2/6009/2020)

And by Lisboa2020, Compete2020 and FEDER through:

* [the CMU|Portugal CAMELOT project](http://wiki.alcidesfonseca.com/research/projects/camelot/) (LISBOA-01-0247-FEDER-045915)


Publications
-----------------

* [Comparing the expressive power of Strongly-Typed and Grammar-Guided Genetic Programming](https://www.researchgate.net/publication/370277603_Comparing_the_expressive_power_of_Strongly-Typed_and_Grammar-Guided_Genetic_Programming) at GECCO'23
* [The Usability Argument for Refinement Typed Genetic Programming](https://link.springer.com/chapter/10.1007/978-3-030-58115-2_2) at PPSN'20

Let us know if your paper uses Aeon, to list it here.

Please cite as:

```
Fonseca, Alcides, Paulo Santos, and Sara Silva. "The usability argument for refinement typed genetic programming." International Conference on Parallel Problem Solving from Nature. Cham: Springer International Publishing, 2020.
```

Bibtex:

```
@inproceedings{fonseca2020usability,
  title={The usability argument for refinement typed genetic programming},
  author={Fonseca, Alcides and Santos, Paulo and Silva, Sara},
  booktitle={International Conference on Parallel Problem Solving from Nature},
  pages={18--32},
  year={2020},
  organization={Springer}
}
```
