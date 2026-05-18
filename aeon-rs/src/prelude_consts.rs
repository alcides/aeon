//! Static prelude constants — port of the small pure-data slice of
//! `aeon.prelude.prelude`. The operator-name lists and the
//! `native_types` Name list move to Rust; the actual Python callables
//! (lambdas, gpu_*, `eval`, `native_import`) and the
//! `typing_vars`/`evaluation_vars` dicts stay Python — they're
//! Python-by-design (live function references, lark-parsed type
//! signatures).

use pyo3::prelude::*;
use pyo3::types::PyList;
use std::sync::OnceLock;

use crate::name::Name;

const INTEGER_ARITHMETIC: &[&str] = &["+", "*", "-", "/", "%"];
const COMPARISON: &[&str] = &["<", ">", "<=", ">="];
const LOGICAL: &[&str] = &["&&", "||"];
const EQUALITY: &[&str] = &["==", "!="];

const NATIVE_TYPES: &[&str] = &[
    "Unit", "Bool", "Int", "Float", "String", "Set", "Tensor", "GpuConfig",
];

fn build_string_list(py: Python<'_>, items: &[&str]) -> Py<PyList> {
    let l = PyList::empty_bound(py);
    for s in items {
        l.append(*s).unwrap();
    }
    l.unbind()
}

fn build_native_types(py: Python<'_>) -> Py<PyList> {
    let l = PyList::empty_bound(py);
    for s in NATIVE_TYPES {
        let n = Py::new(
            py,
            Name { name: s.to_string(), id: 0 },
        )
        .unwrap();
        l.append(n).unwrap();
    }
    l.unbind()
}

#[pyfunction]
pub fn get_integer_arithmetic_operators(py: Python<'_>) -> Py<PyList> {
    static V: OnceLock<Py<PyList>> = OnceLock::new();
    V.get_or_init(|| build_string_list(py, INTEGER_ARITHMETIC)).clone_ref(py)
}

#[pyfunction]
pub fn get_comparison_operators(py: Python<'_>) -> Py<PyList> {
    static V: OnceLock<Py<PyList>> = OnceLock::new();
    V.get_or_init(|| build_string_list(py, COMPARISON)).clone_ref(py)
}

#[pyfunction]
pub fn get_logical_operators(py: Python<'_>) -> Py<PyList> {
    static V: OnceLock<Py<PyList>> = OnceLock::new();
    V.get_or_init(|| build_string_list(py, LOGICAL)).clone_ref(py)
}

#[pyfunction]
pub fn get_equality_operators(py: Python<'_>) -> Py<PyList> {
    static V: OnceLock<Py<PyList>> = OnceLock::new();
    V.get_or_init(|| build_string_list(py, EQUALITY)).clone_ref(py)
}

#[pyfunction]
pub fn get_all_ops(py: Python<'_>) -> Py<PyList> {
    static V: OnceLock<Py<PyList>> = OnceLock::new();
    V.get_or_init(|| {
        let l = PyList::empty_bound(py);
        for group in [INTEGER_ARITHMETIC, COMPARISON, LOGICAL, EQUALITY] {
            for s in group {
                l.append(*s).unwrap();
            }
        }
        l.unbind()
    })
    .clone_ref(py)
}

#[pyfunction]
pub fn get_native_types(py: Python<'_>) -> Py<PyList> {
    static V: OnceLock<Py<PyList>> = OnceLock::new();
    V.get_or_init(|| build_native_types(py)).clone_ref(py)
}
