//! Kind — the universe of types. Mirrors master's `Kind(Enum)` with
//! `BASE` and `STAR` variants.

use pyo3::prelude::*;
use std::sync::OnceLock;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum KindVariant {
    Base,
    Star,
}

impl KindVariant {
    fn name(self) -> &'static str {
        match self {
            KindVariant::Base => "BASE",
            KindVariant::Star => "STAR",
        }
    }

    fn value(self) -> &'static str {
        match self {
            KindVariant::Base => "Β",
            KindVariant::Star => "★",
        }
    }
}

#[pyclass(module = "aeon_rs", frozen)]
pub struct Kind {
    variant: KindVariant,
}

#[pymethods]
impl Kind {
    /// Direct instantiation is blocked — use the singleton class
    /// attributes (`Kind.BASE`, `Kind.STAR`).
    #[new]
    fn py_new() -> PyResult<Self> {
        Err(pyo3::exceptions::PyTypeError::new_err(
            "Kind is an enum — use Kind.BASE or Kind.STAR.",
        ))
    }

    #[classattr]
    #[pyo3(name = "BASE")]
    fn cls_base(py: Python<'_>) -> PyObject {
        base(py)
    }

    #[classattr]
    #[pyo3(name = "STAR")]
    fn cls_star(py: Python<'_>) -> PyObject {
        star(py)
    }

    /// Match Python Enum's `.name` (`"BASE"` / `"STAR"`).
    #[getter]
    fn name(&self) -> &'static str {
        self.variant.name()
    }

    /// Match Python Enum's `.value` (the kind symbol `Β` or `★`).
    #[getter]
    fn value(&self) -> &'static str {
        self.variant.value()
    }

    fn __str__(&self) -> &'static str {
        self.variant.value()
    }

    fn __repr__(&self) -> String {
        format!("Kind.{}", self.variant.name())
    }

    fn __hash__(&self) -> u64 {
        match self.variant {
            KindVariant::Base => 1,
            KindVariant::Star => 2,
        }
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        match other.downcast::<Kind>() {
            Ok(o) => o.borrow().variant == self.variant,
            Err(_) => false,
        }
    }

    fn __ne__(&self, other: &Bound<'_, PyAny>) -> bool {
        !self.__eq__(other)
    }
}

// ---- Singletons ---------------------------------------------------------

struct Singletons {
    base: PyObject,
    star: PyObject,
}

static SINGLETONS: OnceLock<Singletons> = OnceLock::new();

fn singletons(py: Python<'_>) -> &'static Singletons {
    SINGLETONS.get_or_init(|| Singletons {
        base: Py::new(py, Kind { variant: KindVariant::Base })
            .expect("Kind allocation")
            .into_any(),
        star: Py::new(py, Kind { variant: KindVariant::Star })
            .expect("Kind allocation")
            .into_any(),
    })
}

pub fn base(py: Python<'_>) -> PyObject {
    singletons(py).base.clone_ref(py)
}

pub fn star(py: Python<'_>) -> PyObject {
    singletons(py).star.clone_ref(py)
}

/// True iff `k` is `Kind.BASE` (a Rust `Kind` instance, by identity or
/// variant tag — both match since the singletons are cached).
pub fn is_base(py: Python<'_>, k: &PyObject) -> bool {
    let b = k.bind(py);
    if let Ok(kk) = b.downcast::<Kind>() {
        return matches!(kk.borrow().variant, KindVariant::Base);
    }
    false
}

/// True iff `k` is `Kind.STAR`.
pub fn is_star(py: Python<'_>, k: &PyObject) -> bool {
    let b = k.bind(py);
    if let Ok(kk) = b.downcast::<Kind>() {
        return matches!(kk.borrow().variant, KindVariant::Star);
    }
    false
}

// ---- Backwards-compatible factory functions ----------------------------
//
// Pre-Enum Aeon had `BaseKind()` / `StarKind()` callable classes. Some
// callers (notably the lark grammar transformer in earlier Aeon versions)
// still spell them that way. These are exposed as plain functions that
// return the canonical singleton.

#[pyfunction(name = "BaseKind")]
pub fn base_kind_factory(py: Python<'_>) -> PyObject {
    base(py)
}

#[pyfunction(name = "StarKind")]
pub fn star_kind_factory(py: Python<'_>) -> PyObject {
    star(py)
}
