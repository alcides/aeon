//! Registry of inductive constructor groups for SMT distinctness assertions.
//!
//! Populated during inductive expansion (`desugar.expand_inductive_decls`) and
//! consumed during SMT translation (`smt_z3::constructor_distinctness`) so that
//! `Distinct(...)` is asserted for constructor constants of the same inductive
//! type.

use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

use pyo3::prelude::*;
use pyo3::types::{PyDict, PySet};

/// Inductive-type-name → set of prefixed constructor constant names.
type Groups = HashMap<String, Vec<String>>;

static REGISTRY: OnceLock<Mutex<Groups>> = OnceLock::new();

fn registry() -> &'static Mutex<Groups> {
    REGISTRY.get_or_init(|| Mutex::new(HashMap::new()))
}

#[pyfunction]
pub fn register_constructors(type_name: &str, constructor_names: Vec<String>) {
    registry()
        .lock()
        .unwrap()
        .insert(type_name.to_string(), constructor_names);
}

#[pyfunction]
pub fn get_constructor_groups(py: Python<'_>) -> PyResult<Py<PyDict>> {
    let groups = registry().lock().unwrap();
    let out = PyDict::new_bound(py);
    for (k, v) in groups.iter() {
        let s = PySet::empty_bound(py)?;
        for name in v {
            s.add(name)?;
        }
        out.set_item(k, s)?;
    }
    Ok(out.unbind())
}

#[pyfunction]
pub fn clear_constructor_registry() {
    registry().lock().unwrap().clear();
}

/// Internal Rust accessor for [`smt_z3::constructor_distinctness`] — avoids
/// the Python round-trip every leaf translation would otherwise make.
pub fn snapshot() -> Vec<(String, Vec<String>)> {
    registry()
        .lock()
        .unwrap()
        .iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect()
}
