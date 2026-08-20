//! Helper for default Location values. The Location pyclasses live in
//! `crate::location`; this module just memoises the
//! `SynthesizedLocation("default")` singleton used by Rust-constructed
//! AST nodes.

use pyo3::prelude::*;
use std::sync::OnceLock;

use crate::location::{Location, SynthesizedLocation};

static DEFAULT_LOC: OnceLock<PyObject> = OnceLock::new();

/// Returns the `SynthesizedLocation("default")` singleton. Constructed
/// directly from Rust — no Python round trip.
pub fn default_location(py: Python<'_>) -> PyObject {
    if let Some(obj) = DEFAULT_LOC.get() {
        return obj.clone_ref(py);
    }
    let obj = Py::new(
        py,
        (SynthesizedLocation { reason: "default".to_string() }, Location),
    )
    .expect("SynthesizedLocation allocation")
    .into_any();
    let _ = DEFAULT_LOC.set(obj.clone_ref(py));
    obj
}

/// Resolve an optional `loc` parameter to a concrete Location.
pub fn resolve_loc(py: Python<'_>, loc: Option<PyObject>) -> PyObject {
    loc.unwrap_or_else(|| default_location(py))
}
