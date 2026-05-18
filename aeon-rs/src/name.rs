//! Name: a (string, id) pair used throughout the Aeon AST. Mirrors aeon.utils.name.

use pyo3::prelude::*;
use pyo3::types::PyTuple;
use std::sync::atomic::{AtomicI64, Ordering};

#[pyclass(module = "aeon_rs", frozen)]
#[derive(Clone)]
pub struct Name {
    #[pyo3(get)]
    pub name: String,
    #[pyo3(get)]
    pub id: i64,
}

#[pymethods]
impl Name {
    #[new]
    #[pyo3(signature = (name, id = -1))]
    fn py_new(name: &str, id: i64) -> Self {
        Name { name: name.trim().to_string(), id }
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "id"])
    }

    pub fn __str__(&self) -> String {
        if self.id == 0 {
            self.name.clone()
        } else if self.id == -1 {
            format!("{}?", self.name)
        } else {
            format!("{}{}", self.name, superscript(self.id))
        }
    }

    fn __repr__(&self) -> String {
        self.__str__()
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        match other.downcast::<Name>() {
            Ok(o) => {
                let o = o.borrow();
                self.id == o.id && self.name == o.name
            }
            Err(_) => false,
        }
    }

    fn __ne__(&self, other: &Bound<'_, PyAny>) -> bool {
        !self.__eq__(other)
    }

    fn __hash__(&self) -> u64 {
        // Stable hash matching Python's dataclass(unsafe_hash=True)-equivalent
        // is impossible, but consistency with __eq__ is what matters.
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut h = DefaultHasher::new();
        self.name.hash(&mut h);
        self.id.hash(&mut h);
        h.finish()
    }

    fn __lt__(&self, other: &Name) -> bool {
        self.id < other.id
    }

    pub fn pretty(&self) -> String {
        self.name.clone()
    }

    fn __reduce__<'py>(slf: &Bound<'py, Self>) -> PyResult<(PyObject, (String, i64))> {
        let py = slf.py();
        let cls: PyObject = slf.get_type().into();
        let s = slf.borrow();
        Ok((cls, (s.name.clone(), s.id)))
    }
}

fn superscript(n: i64) -> String {
    let digits = ['⁰', '¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹'];
    let s = n.to_string();
    let mut out = String::new();
    for ch in s.chars() {
        match ch {
            '0'..='9' => out.push(digits[ch.to_digit(10).unwrap() as usize]),
            '-' => out.push('⁻'),
            _ => out.push(ch),
        }
    }
    out
}

// FreshCounter — a tiny stateful counter exposed to Python. The original
// Python uses a singleton; we expose the class but the canonical instance
// lives on the Python side.
#[pyclass(module = "aeon_rs")]
pub struct FreshCounter {
    counter: AtomicI64,
}

#[pymethods]
impl FreshCounter {
    #[new]
    fn py_new() -> Self {
        FreshCounter { counter: AtomicI64::new(0) }
    }

    fn fresh(&self) -> i64 {
        self.counter.fetch_add(1, Ordering::Relaxed) + 1
    }

    #[getter]
    fn counter(&self) -> i64 {
        self.counter.load(Ordering::Relaxed)
    }

    #[setter]
    fn set_counter(&self, v: i64) {
        self.counter.store(v, Ordering::Relaxed)
    }
}

/// Call the canonical `aeon.utils.name.fresh_counter.fresh()` and return its
/// new value. This is the singleton used everywhere in the codebase to mint
/// fresh `Name.id`s, so any Rust code that needs a fresh id must route
/// through it (a Rust-local counter would diverge).
pub fn next_fresh_id(py: Python<'_>) -> PyResult<i64> {
    let module = py.import_bound("aeon.utils.name")?;
    let counter = module.getattr("fresh_counter")?;
    let v = counter.call_method0("fresh")?;
    v.extract::<i64>()
}
