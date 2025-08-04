# Aeon Development FAQ

This is a list of questions (and responses) that may come up while developing for the first time on **Aeon**.

---

### How to install?

#### Requirements:

- [Uv](https://github.com/astral-sh/uv)
- [Pre-Commit](https://pre-commit.com/)

#### Installation:

After cloning the project run `uv pip install -e` and `uvx pre-commit install`

#### Running the project and test

- To run a .ae file run the command `uv run python -m aeon [flags] [file]`
- to run the tests use `uv run pytest`

---

### What is the difference between the `STypes` and `Types` classes?

- The `Types` class represents the **Core Language**. These types are part of the internal implementation and should **never be exposed** to the user.

- The `STypes` class represents the **Sugar Language** (also called the **Surface Language**). These are types that are safe to expose and interact with in external code or tooling.
