Aeon Programming Language
=========================

Alcides Fonseca <me@alcidesfonseca.com>


Aeon is a programming language with syntax support for full dependent types, of which refined types are typechecked.

Aeon is implemented in Python using parsec, and generates Java source code. Aeon supports native bindings.

-----------

How to use:

* Requires python3
* Requires z3 (with python3 bindings)
* Requires everything in requirements.pip
* Requires Java7+

```
brew install --with-python z3
pip3 install -r requirements.pip
```

```
./ae examples/integral.p
```