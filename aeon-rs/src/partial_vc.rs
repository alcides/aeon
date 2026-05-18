//! Modular verification conditions for liquid typechecking fragments
//! (port of `aeon.typechecking.partial_vc`).

use pyo3::prelude::*;
use pyo3::types::PyList;

use crate::typectx::TypingContext;

#[pyclass(module = "aeon_rs", frozen)]
pub struct ModularVC {
    #[pyo3(get)]
    pub context: PyObject,
    #[pyo3(get)]
    pub term: PyObject,
    #[pyo3(get)]
    pub expected: PyObject,
    #[pyo3(get)]
    pub constraint: PyObject,
}

#[pymethods]
impl ModularVC {
    #[new]
    fn py_new(context: PyObject, term: PyObject, expected: PyObject, constraint: PyObject) -> Self {
        ModularVC { context, term, expected, constraint }
    }

    #[getter]
    fn lifted(&self, py: Python<'_>) -> PyResult<PyObject> {
        let ctx_bound = self.context.bind(py).downcast::<TypingContext>()?.clone();
        crate::entailment::entailment_context(py, &ctx_bound, self.constraint.clone_ref(py))
    }

    fn entails(&self, py: Python<'_>) -> PyResult<bool> {
        let ctx_bound = self.context.bind(py).downcast::<TypingContext>()?.clone();
        crate::entailment::entailment(py, &ctx_bound, self.constraint.clone_ref(py))
    }

    #[pyo3(signature = (qualifier_atoms, typing_ctx = None))]
    fn entails_with_qualifiers(
        &self,
        py: Python<'_>,
        qualifier_atoms: PyObject,
        typing_ctx: Option<PyObject>,
    ) -> PyResult<bool> {
        let lifted = self.lifted(py)?;
        let tctx: PyObject = match typing_ctx {
            Some(t) => t,
            None => self.context.clone_ref(py),
        };
        crate::horn::solve(py, lifted, Some(tctx), Some(qualifier_atoms))
    }

    #[pyo3(signature = (typing_ctx = None))]
    fn explain_failures(
        &self,
        py: Python<'_>,
        typing_ctx: Option<PyObject>,
    ) -> PyResult<Py<PyList>> {
        let lifted = self.lifted(py)?;
        let ctx = typing_ctx.unwrap_or_else(|| self.context.clone_ref(py));
        crate::typeinfer::constraint_to_parts(py, lifted, Some(ctx))
    }
}

#[pyfunction]
pub fn build_modular_vc(
    py: Python<'_>,
    ctx: &Bound<'_, TypingContext>,
    term: PyObject,
    expected: PyObject,
) -> PyResult<ModularVC> {
    let ctx_py: Py<TypingContext> = ctx.clone().unbind();
    let sk = Py::new(py, (crate::kind::StarKind, crate::kind::Kind))?.into_any();
    if !crate::well_formed::wellformed(py, &ctx_py, &expected, &sk)? {
        let api = py.import_bound("aeon.facade.api")?;
        let cls = api.getattr("CoreWellformnessError")?;
        let err = cls.call1((expected,))?;
        return Err(PyErr::from_value_bound(err));
    }
    let c = crate::typeinfer::check(py, ctx, term.clone_ref(py), expected.clone_ref(py))?;
    Ok(ModularVC {
        context: ctx.clone().into_any().unbind(),
        term,
        expected,
        constraint: c,
    })
}
