//! Source-location types — port of `aeon.utils.location`.
//!
//! `Location` is the abstract base; `FileLocation` carries a file path and
//! `(line, col)` start/end pairs from the lark parser; `SynthesizedLocation`
//! is the no-file marker used by Rust-constructed AST nodes (the default
//! one is `SynthesizedLocation("default")`).

use pyo3::prelude::*;
use pyo3::types::PyTuple;

#[pyclass(module = "aeon_rs", subclass)]
pub struct Location;

#[pymethods]
impl Location {
    #[new]
    fn py_new() -> Self {
        Location
    }
}

#[pyclass(module = "aeon_rs", extends = Location, frozen)]
pub struct FileLocation {
    /// `file` mirrors the Python dataclass field, which is typed `str`
    /// but in practice receives `None` for in-memory sources (the lark
    /// transformer passes `file=None` for buffer-only parses). Storing
    /// it as `PyObject` preserves that liberal contract.
    #[pyo3(get)]
    pub file: PyObject,
    /// `(line, col)` start coordinate.
    #[pyo3(get)]
    pub start: (i64, i64),
    /// `(line, col)` end coordinate.
    #[pyo3(get)]
    pub end: (i64, i64),
}

#[pymethods]
impl FileLocation {
    #[new]
    fn py_new(file: PyObject, start: (i64, i64), end: (i64, i64)) -> (Self, Location) {
        (FileLocation { file, start, end }, Location)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["file", "start", "end"])
    }

    fn get_start(&self) -> (i64, i64) {
        self.start
    }

    fn get_end(&self) -> (i64, i64) {
        self.end
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "FileLocation({}, {:?}, {:?})",
            self.file.bind(py).repr()?,
            self.start,
            self.end
        ))
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<FileLocation>() {
            Ok(o) => {
                let o = o.borrow();
                Ok(self.file.bind(py).eq(o.file.bind(py))?
                    && self.start == o.start
                    && self.end == o.end)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(&self, py: Python<'_>) -> PyResult<u64> {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut h = DefaultHasher::new();
        let fh: isize = self.file.bind(py).hash()?;
        fh.hash(&mut h);
        self.start.hash(&mut h);
        self.end.hash(&mut h);
        Ok(h.finish())
    }
}

#[pyclass(module = "aeon_rs", extends = Location, frozen)]
pub struct SynthesizedLocation {
    #[pyo3(get)]
    pub reason: String,
}

#[pymethods]
impl SynthesizedLocation {
    #[new]
    fn py_new(reason: String) -> (Self, Location) {
        (SynthesizedLocation { reason }, Location)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["reason"])
    }

    fn get_start(&self) -> (i64, i64) {
        (0, 0)
    }

    fn get_end(&self) -> (i64, i64) {
        (0, 0)
    }

    fn __repr__(&self) -> String {
        format!("SynthesizedLocation({:?})", self.reason)
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        match other.downcast::<SynthesizedLocation>() {
            Ok(o) => self.reason == o.borrow().reason,
            Err(_) => false,
        }
    }

    fn __hash__(&self) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut h = DefaultHasher::new();
        self.reason.hash(&mut h);
        h.finish()
    }
}
