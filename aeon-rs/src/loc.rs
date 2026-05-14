//! Helper for default Location values. Locations themselves stay in Python.

use pyo3::prelude::*;
use std::sync::OnceLock;

static DEFAULT_LOC: OnceLock<PyObject> = OnceLock::new();

/// Returns the default SynthesizedLocation("default") singleton.
/// The first call constructs it by importing from Python; subsequent calls reuse.
pub fn default_location(py: Python<'_>) -> PyObject {
    if let Some(obj) = DEFAULT_LOC.get() {
        return obj.clone_ref(py);
    }
    let module = py
        .import_bound("aeon.utils.location")
        .expect("aeon.utils.location must be importable");
    let cls = module
        .getattr("SynthesizedLocation")
        .expect("SynthesizedLocation must exist");
    let inst = cls
        .call1(("default",))
        .expect("SynthesizedLocation('default') must construct");
    let obj: PyObject = inst.into();
    let _ = DEFAULT_LOC.set(obj.clone_ref(py));
    obj
}

/// Resolve an optional loc parameter to a concrete Python Location.
pub fn resolve_loc(py: Python<'_>, loc: Option<PyObject>) -> PyObject {
    loc.unwrap_or_else(|| default_location(py))
}
