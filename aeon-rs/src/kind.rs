//! Kind hierarchy. Mirrors aeon.core.types.Kind / BaseKind / StarKind.

use pyo3::prelude::*;

#[pyclass(module = "aeon_rs", subclass, frozen)]
pub struct Kind;

#[pymethods]
impl Kind {
    #[new]
    fn py_new() -> Self {
        Kind
    }

    fn __repr__(slf: &Bound<'_, Self>) -> PyResult<String> {
        slf.call_method0("__str__")?.extract::<String>()
    }
}

#[pyclass(module = "aeon_rs", extends = Kind, frozen)]
pub struct BaseKind;

#[pymethods]
impl BaseKind {
    #[new]
    fn py_new() -> (Self, Kind) {
        (BaseKind, Kind)
    }

    fn __str__(&self) -> &'static str {
        "Β"
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other.is_instance_of::<BaseKind>()
    }

    fn __hash__(&self) -> u64 {
        1
    }
}

#[pyclass(module = "aeon_rs", extends = Kind, frozen)]
pub struct StarKind;

#[pymethods]
impl StarKind {
    #[new]
    fn py_new() -> (Self, Kind) {
        (StarKind, Kind)
    }

    fn __str__(&self) -> &'static str {
        "★"
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other.is_instance_of::<StarKind>()
    }

    fn __hash__(&self) -> u64 {
        2
    }
}
