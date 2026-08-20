//! QTT multiplicity semiring (port of `aeon.core.multiplicity`).
//!
//! The Python original is an `Enum` whose four members are exposed as
//! module-level singletons `M0`, `M1`, `MOmega`, `MN`. Callers (including
//! cross-module Rust callers in `linearity.rs`, `evaluator.rs`, etc.) rely
//! on identity (`is`) comparisons, so this port preserves that semantics:
//! the four module attributes are the *same* `Py<Multiplicity>` objects on
//! every access, cached at module load.

use pyo3::prelude::*;
use pyo3::types::PyType;
use std::sync::OnceLock;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum MultVariant {
    M0,
    M1,
    MOmega,
    MN,
}

impl MultVariant {
    fn token(self) -> &'static str {
        match self {
            MultVariant::M0 => "0",
            MultVariant::M1 => "1",
            MultVariant::MOmega => "ω",
            MultVariant::MN => "n",
        }
    }

    fn name(self) -> &'static str {
        match self {
            MultVariant::M0 => "M0",
            MultVariant::M1 => "M1",
            MultVariant::MOmega => "MOmega",
            MultVariant::MN => "MN",
        }
    }
}

#[pyclass(module = "aeon_rs", frozen)]
pub struct Multiplicity {
    variant: MultVariant,
}

#[pymethods]
impl Multiplicity {
    #[new]
    /// Block direct construction — callers must use the cached singletons.
    fn py_new() -> PyResult<Self> {
        Err(pyo3::exceptions::PyTypeError::new_err(
            "Multiplicity is a singleton — use M0, M1, MOmega, or MN.",
        ))
    }

    fn __repr__(&self) -> &'static str {
        self.variant.token()
    }

    fn __str__(&self) -> &'static str {
        self.variant.token()
    }

    fn __hash__(&self) -> u64 {
        // Distinct hash per variant so dict-keyed-by-multiplicity works.
        match self.variant {
            MultVariant::M0 => 0,
            MultVariant::M1 => 1,
            MultVariant::MOmega => 2,
            MultVariant::MN => 3,
        }
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        match other.downcast::<Multiplicity>() {
            Ok(o) => o.borrow().variant == self.variant,
            Err(_) => false,
        }
    }

    fn __ne__(&self, other: &Bound<'_, PyAny>) -> bool {
        !self.__eq__(other)
    }

    /// `Multiplicity.M0`, etc. mirrored from the original Python Enum so
    /// `Multiplicity.M0 is M0` round-trips through the class object.
    #[classattr]
    #[pyo3(name = "M0")]
    fn cls_m0(py: Python<'_>) -> PyObject {
        m0(py)
    }
    #[classattr]
    #[pyo3(name = "M1")]
    fn cls_m1(py: Python<'_>) -> PyObject {
        m1(py)
    }
    #[classattr]
    #[pyo3(name = "MOmega")]
    fn cls_momega(py: Python<'_>) -> PyObject {
        momega(py)
    }
    #[classattr]
    #[pyo3(name = "MN")]
    fn cls_mn(py: Python<'_>) -> PyObject {
        mn(py)
    }

    /// Match Python Enum's `.value` attribute (used by formatters / repr).
    #[getter]
    fn value(&self) -> &'static str {
        self.variant.token()
    }

    /// Match Python Enum's `.name` attribute.
    #[getter]
    fn name(&self) -> &'static str {
        self.variant.name()
    }
}

// ---- Singleton machinery -------------------------------------------------

struct Singletons {
    m0: PyObject,
    m1: PyObject,
    momega: PyObject,
    mn: PyObject,
}

static SINGLETONS: OnceLock<Singletons> = OnceLock::new();

fn singletons(py: Python<'_>) -> &'static Singletons {
    SINGLETONS.get_or_init(|| {
        let mk = |v: MultVariant| -> PyObject {
            Py::new(py, Multiplicity { variant: v })
                .expect("Multiplicity allocation")
                .into_any()
        };
        Singletons {
            m0: mk(MultVariant::M0),
            m1: mk(MultVariant::M1),
            momega: mk(MultVariant::MOmega),
            mn: mk(MultVariant::MN),
        }
    })
}

pub fn m0(py: Python<'_>) -> PyObject {
    singletons(py).m0.clone_ref(py)
}
pub fn m1(py: Python<'_>) -> PyObject {
    singletons(py).m1.clone_ref(py)
}
pub fn momega(py: Python<'_>) -> PyObject {
    singletons(py).momega.clone_ref(py)
}
pub fn mn(py: Python<'_>) -> PyObject {
    singletons(py).mn.clone_ref(py)
}

/// Return the internal variant of any `Multiplicity` PyObject.
fn variant_of(py: Python<'_>, m: &PyObject) -> Option<MultVariant> {
    m.bind(py)
        .downcast::<Multiplicity>()
        .ok()
        .map(|b| b.borrow().variant)
}

fn from_variant(py: Python<'_>, v: MultVariant) -> PyObject {
    match v {
        MultVariant::M0 => m0(py),
        MultVariant::M1 => m1(py),
        MultVariant::MOmega => momega(py),
        MultVariant::MN => mn(py),
    }
}

// ---- Public Rust API used by linearity.rs, evaluator.rs, etc. -----------

/// Semiring addition.
pub fn add_variant(a: MultVariant, b: MultVariant) -> MultVariant {
    // MN collapses to M1 for arithmetic.
    let a = if matches!(a, MultVariant::MN) { MultVariant::M1 } else { a };
    let b = if matches!(b, MultVariant::MN) { MultVariant::M1 } else { b };
    match (a, b) {
        (MultVariant::M0, x) | (x, MultVariant::M0) => x,
        (MultVariant::MOmega, _) | (_, MultVariant::MOmega) => MultVariant::MOmega,
        // both are M1
        (MultVariant::M1, MultVariant::M1) => MultVariant::MOmega,
        _ => MultVariant::MOmega,
    }
}

/// Semiring multiplication.
pub fn mul_variant(a: MultVariant, b: MultVariant) -> MultVariant {
    // MN is identity on either side.
    if matches!(a, MultVariant::MN) {
        return b;
    }
    if matches!(b, MultVariant::MN) {
        return a;
    }
    match (a, b) {
        (MultVariant::M0, _) | (_, MultVariant::M0) => MultVariant::M0,
        (MultVariant::M1, x) | (x, MultVariant::M1) => x,
        _ => MultVariant::MOmega,
    }
}

// ---- Python-facing functions --------------------------------------------

/// Semiring addition — combine usage tallies in a single scope.
#[pyfunction]
pub fn add(py: Python<'_>, a: PyObject, b: PyObject) -> PyResult<PyObject> {
    let va = variant_of(py, &a).ok_or_else(|| {
        pyo3::exceptions::PyTypeError::new_err("add: first arg is not a Multiplicity")
    })?;
    let vb = variant_of(py, &b).ok_or_else(|| {
        pyo3::exceptions::PyTypeError::new_err("add: second arg is not a Multiplicity")
    })?;
    Ok(from_variant(py, add_variant(va, vb)))
}

/// Semiring multiplication — combine outer/inner multiplicity.
#[pyfunction]
pub fn mul(py: Python<'_>, a: PyObject, b: PyObject) -> PyResult<PyObject> {
    let va = variant_of(py, &a).ok_or_else(|| {
        pyo3::exceptions::PyTypeError::new_err("mul: first arg is not a Multiplicity")
    })?;
    let vb = variant_of(py, &b).ok_or_else(|| {
        pyo3::exceptions::PyTypeError::new_err("mul: second arg is not a Multiplicity")
    })?;
    Ok(from_variant(py, mul_variant(va, vb)))
}

/// Parse a surface-syntax multiplicity token.
#[pyfunction]
pub fn multiplicity_from_token(py: Python<'_>, tok: &str) -> PyResult<PyObject> {
    let v = match tok {
        "0" => MultVariant::M0,
        "1" => MultVariant::M1,
        "omega" | "ω" => MultVariant::MOmega,
        "n" => MultVariant::MN,
        _ => {
            return Err(pyo3::exceptions::PyValueError::new_err(format!(
                "Not a multiplicity token: {:?}", tok
            )));
        }
    };
    Ok(from_variant(py, v))
}

// ---- Identity helpers for native Rust callers ---------------------------

pub fn is_m0(py: Python<'_>, m: &PyObject) -> bool {
    variant_of(py, m).map_or(false, |v| matches!(v, MultVariant::M0))
}
pub fn is_m1(py: Python<'_>, m: &PyObject) -> bool {
    variant_of(py, m).map_or(false, |v| matches!(v, MultVariant::M1))
}
pub fn is_momega(py: Python<'_>, m: &PyObject) -> bool {
    variant_of(py, m).map_or(false, |v| matches!(v, MultVariant::MOmega))
}
pub fn is_mn(py: Python<'_>, m: &PyObject) -> bool {
    variant_of(py, m).map_or(false, |v| matches!(v, MultVariant::MN))
}

// Silence unused-import warning if PyType ever becomes unreferenced.
#[allow(dead_code)]
fn _force_use(_py: Python<'_>, _t: Bound<'_, PyType>) {}
