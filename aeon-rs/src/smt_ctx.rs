//! SMTContext and CanonicConstraint pyclasses.
//!
//! Pure data: track sorts, functions, variables, premises, and reflected
//! functions during the flatten/translate pipeline. The `with_*` builders
//! return a new SMTContext with one entry added (copy-on-write).
//!
//! Mirrors aeon.verification.smt.SMTContext / CanonicConstraint.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList};

use crate::liquid::{LiquidApp, LiquidLiteralBool, LiquidTerm};
use crate::name::Name;

/// Build a fresh `LiquidLiteralBool(true)` instance.
fn liquid_true(py: Python<'_>) -> PyResult<PyObject> {
    let loc = crate::loc::default_location(py);
    crate::builders::new_liquid_literal_bool(py, true, loc)
}

/// `mk_liquid_and(e1, e2)` — short-circuit AND, mirrors aeon.core.liquid_ops.
pub fn mk_liquid_and(py: Python<'_>, e1: PyObject, e2: PyObject) -> PyResult<PyObject> {
    // We compare structurally by attempting downcast to LiquidLiteralBool.
    let e1b = e1.bind(py);
    let e2b = e2.bind(py);

    if let Ok(b1) = e1b.downcast::<LiquidLiteralBool>() {
        let b1 = b1.borrow();
        if b1.value {
            return Ok(e2);
        }
        // e1 is False — short-circuit to False.
        return Ok(e1);
    }
    if let Ok(b2) = e2b.downcast::<LiquidLiteralBool>() {
        let b2 = b2.borrow();
        if b2.value {
            return Ok(e1);
        }
        // e2 is False — short-circuit to False.
        return Ok(e2);
    }

    // Otherwise LiquidApp("&&", [e1, e2]).
    let and_name = Py::new(py, Name { name: "&&".to_string(), id: 0 })?;
    let args = PyList::new_bound(py, &[e1, e2]).unbind();
    let loc = crate::loc::default_location(py);
    crate::builders::new_liquid_app(py, and_name, args, loc)
}

// =============================================================================
// SMTContext
// =============================================================================

#[pyclass(module = "aeon_rs")]
pub struct SMTContext {
    /// `list[str]` — declared sort names.
    #[pyo3(get)]
    pub sorts: Py<PyList>,
    /// `dict[str, AbstractionType]` — uninterpreted/reflected function types.
    #[pyo3(get)]
    pub functions: Py<PyDict>,
    /// `dict[str, TypeConstructor]` — variables in scope.
    #[pyo3(get)]
    pub variables: Py<PyDict>,
    /// `list[LiquidTerm]` — accumulated premises.
    #[pyo3(get)]
    pub premises: Py<PyList>,
    /// `dict[str, tuple[tuple[Name, ...], LiquidTerm]]` — reflected functions.
    #[pyo3(get)]
    pub reflected_functions: Py<PyDict>,
}

#[pymethods]
impl SMTContext {
    #[new]
    #[pyo3(signature = (sorts, functions, variables, premises, reflected_functions))]
    fn py_new(
        sorts: Py<PyList>,
        functions: Py<PyDict>,
        variables: Py<PyDict>,
        premises: Py<PyList>,
        reflected_functions: Py<PyDict>,
    ) -> Self {
        SMTContext {
            sorts,
            functions,
            variables,
            premises,
            reflected_functions,
        }
    }

    pub fn with_sort(&self, py: Python<'_>, name: &Bound<'_, PyAny>) -> PyResult<SMTContext> {
        let new_sorts = PyList::empty_bound(py);
        let s = self.sorts.bind(py);
        for i in 0..s.len() {
            new_sorts.append(s.get_item(i)?)?;
        }
        new_sorts.append(name.str()?)?;
        Ok(SMTContext {
            sorts: new_sorts.unbind(),
            functions: self.functions.clone_ref(py),
            variables: self.variables.clone_ref(py),
            premises: self.premises.clone_ref(py),
            reflected_functions: self.reflected_functions.clone_ref(py),
        })
    }

    pub fn with_function(
        &self,
        py: Python<'_>,
        name: &Bound<'_, PyAny>,
        ty: PyObject,
    ) -> PyResult<SMTContext> {
        let new_funs = self.functions.bind(py).copy()?;
        new_funs.set_item(name.str()?, ty)?;
        Ok(SMTContext {
            sorts: self.sorts.clone_ref(py),
            functions: new_funs.unbind(),
            variables: self.variables.clone_ref(py),
            premises: self.premises.clone_ref(py),
            reflected_functions: self.reflected_functions.clone_ref(py),
        })
    }

    pub fn with_var(
        &self,
        py: Python<'_>,
        name: &Bound<'_, PyAny>,
        ty: PyObject,
    ) -> PyResult<SMTContext> {
        let new_vars = self.variables.bind(py).copy()?;
        new_vars.set_item(name.str()?, ty)?;
        Ok(SMTContext {
            sorts: self.sorts.clone_ref(py),
            functions: self.functions.clone_ref(py),
            variables: new_vars.unbind(),
            premises: self.premises.clone_ref(py),
            reflected_functions: self.reflected_functions.clone_ref(py),
        })
    }

    pub fn with_premise(&self, py: Python<'_>, p: PyObject) -> PyResult<SMTContext> {
        let new_prem = PyList::empty_bound(py);
        let ps = self.premises.bind(py);
        for i in 0..ps.len() {
            new_prem.append(ps.get_item(i)?)?;
        }
        new_prem.append(p)?;
        Ok(SMTContext {
            sorts: self.sorts.clone_ref(py),
            functions: self.functions.clone_ref(py),
            variables: self.variables.clone_ref(py),
            premises: new_prem.unbind(),
            reflected_functions: self.reflected_functions.clone_ref(py),
        })
    }

    pub fn with_reflected_function(
        &self,
        py: Python<'_>,
        name: &Bound<'_, PyAny>,
        params: PyObject,
        body: PyObject,
    ) -> PyResult<SMTContext> {
        let new_refs = self.reflected_functions.bind(py).copy()?;
        let tup = pyo3::types::PyTuple::new_bound(py, &[params, body]);
        new_refs.set_item(name.str()?, tup)?;
        Ok(SMTContext {
            sorts: self.sorts.clone_ref(py),
            functions: self.functions.clone_ref(py),
            variables: self.variables.clone_ref(py),
            premises: self.premises.clone_ref(py),
            reflected_functions: new_refs.unbind(),
        })
    }
}

// =============================================================================
// CanonicConstraint
// =============================================================================

#[pyclass(module = "aeon_rs")]
pub struct CanonicConstraint {
    #[pyo3(get)]
    pub sorts: Py<PyList>,
    #[pyo3(get)]
    pub functions: Py<PyDict>,
    #[pyo3(get)]
    pub variables: Py<PyDict>,
    #[pyo3(get)]
    pub premise: PyObject,
    #[pyo3(get)]
    pub conclusion: PyObject,
}

#[pymethods]
impl CanonicConstraint {
    #[new]
    pub fn py_new(py: Python<'_>, ctx: &SMTContext, pos: PyObject) -> PyResult<Self> {
        // premise = reduce(mk_liquid_and, ctx.premises, LiquidLiteralBool(True))
        let mut premise = liquid_true(py)?;
        let ps = ctx.premises.bind(py);
        for i in 0..ps.len() {
            let p = ps.get_item(i)?.unbind();
            premise = mk_liquid_and(py, premise, p)?;
        }

        Ok(CanonicConstraint {
            sorts: ctx.sorts.clone_ref(py),
            functions: ctx.functions.clone_ref(py),
            variables: ctx.variables.clone_ref(py),
            premise,
            conclusion: pos,
        })
    }
}

/// Build a fresh empty SMTContext (`SMTContext(["Top"], {}, {}, [], {})`).
/// Used by `flatten(c, ctx=None)`.
pub fn empty_smt_context(py: Python<'_>) -> PyResult<Py<SMTContext>> {
    let sorts = PyList::new_bound(py, &["Top"]).unbind();
    let functions = PyDict::new_bound(py).unbind();
    let variables = PyDict::new_bound(py).unbind();
    let premises = PyList::empty_bound(py).unbind();
    let reflected_functions = PyDict::new_bound(py).unbind();
    Py::new(
        py,
        SMTContext {
            sorts,
            functions,
            variables,
            premises,
            reflected_functions,
        },
    )
}

#[allow(dead_code)]
fn _silence_unused(_l: &LiquidApp, _t: &LiquidTerm) {}
