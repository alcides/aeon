//! Runtime evaluator (port of `aeon.backend.evaluator`).
//!
//! Values are arbitrary Python objects — Rust holds them as `PyObject`s
//! and goes through the Python ABI for application (`f(arg)`) and the
//! native-FFI escape hatch (`native "..."`, which `real_eval`s the string
//! as Python code).

use std::collections::HashMap;

use pyo3::prelude::*;
use pyo3::types::PyDict;

use crate::name::Name;
use crate::terms::{
    Abstraction, Annotation, Application, Hole, If, Let, Literal, Rec, RefinementAbstraction,
    RefinementApplication, TypeAbstraction, TypeApplication, Var,
};

#[derive(Clone, PartialEq, Eq, Hash)]
struct NameKey {
    name: String,
    id: i64,
}

fn name_key(py: Python<'_>, n: &Py<Name>) -> NameKey {
    let n = n.borrow(py);
    NameKey { name: n.name.clone(), id: n.id }
}

// =============================================================================
// EvaluationContext
// =============================================================================

#[pyclass(module = "aeon_rs")]
pub struct EvaluationContext {
    /// `dict[Name, Any]` — values for in-scope variables.
    #[pyo3(get, set)]
    pub variables: Py<PyDict>,
    #[pyo3(get, set)]
    pub metadata: Option<PyObject>,
    #[pyo3(get, set)]
    pub pipeline: Option<PyObject>,
}

#[pymethods]
impl EvaluationContext {
    #[new]
    #[pyo3(signature = (prev = None, metadata = None, pipeline = None))]
    fn py_new(
        py: Python<'_>,
        prev: Option<Py<PyDict>>,
        metadata: Option<PyObject>,
        pipeline: Option<PyObject>,
    ) -> PyResult<Self> {
        let variables = match prev {
            Some(p) => p.bind(py).copy()?.unbind(),
            None => PyDict::new_bound(py).unbind(),
        };
        Ok(EvaluationContext { variables, metadata, pipeline })
    }

    fn with_var(
        &self,
        py: Python<'_>,
        name: Py<Name>,
        value: PyObject,
    ) -> PyResult<EvaluationContext> {
        let new_vars = self.variables.bind(py).copy()?;
        new_vars.set_item(name, value)?;
        Ok(EvaluationContext {
            variables: new_vars.unbind(),
            metadata: self.metadata.as_ref().map(|m| m.clone_ref(py)),
            pipeline: self.pipeline.as_ref().map(|p| p.clone_ref(py)),
        })
    }

    fn get(&self, py: Python<'_>, name: Py<Name>) -> PyResult<PyObject> {
        let value = self.variables.bind(py).get_item(name)?;
        Ok(value.unwrap().unbind())
    }
}

// =============================================================================
// is_native_var / is_native_import
// =============================================================================

fn real_eval(py: Python<'_>) -> PyResult<PyObject> {
    Ok(py.import_bound("builtins")?.getattr("eval")?.unbind())
}

fn is_native_var(py: Python<'_>, fun: &PyObject) -> bool {
    real_eval(py)
        .map(|r| fun.bind(py).is(r.bind(py)))
        .unwrap_or(false)
}

fn is_native_import(py: Python<'_>, fun: &PyObject) -> bool {
    let bound = fun.bind(py);
    if let Ok(tap) = bound.downcast::<TypeApplication>() {
        let inner = tap.borrow().body.clone_ref(py);
        return is_native_import(py, &inner);
    }
    if let Ok(v) = bound.downcast::<Var>() {
        return v.borrow().name.borrow(py).name == "native_import";
    }
    false
}

// =============================================================================
// eval
// =============================================================================

fn is_m0(py: Python<'_>, m: &PyObject) -> bool {
    let mult_mod = py.import_bound("aeon.core.multiplicity");
    if let Ok(mm) = mult_mod {
        if let Ok(m0) = mm.getattr("M0") {
            return m.bind(py).is(&m0);
        }
    }
    false
}

#[pyfunction]
#[pyo3(signature = (t, ctx = None))]
pub fn eval(
    py: Python<'_>,
    t: PyObject,
    ctx: Option<&Bound<'_, EvaluationContext>>,
) -> PyResult<PyObject> {
    let ctx_owned: Py<EvaluationContext> = match ctx {
        Some(c) => c.clone().unbind(),
        None => Py::new(py, EvaluationContext::py_new(py, None, None, None)?)?,
    };
    eval_inner(py, t, ctx_owned)
}

fn eval_inner(py: Python<'_>, t: PyObject, ctx: Py<EvaluationContext>) -> PyResult<PyObject> {
    let bound = t.bind(py);

    if let Ok(lit) = bound.downcast::<Literal>() {
        return Ok(lit.borrow().value.clone_ref(py));
    }

    if let Ok(v) = bound.downcast::<Var>() {
        let n = v.borrow().name.clone_ref(py);
        return ctx.borrow(py).get(py, n);
    }

    if let Ok(ab) = bound.downcast::<Abstraction>() {
        let ab = ab.borrow();
        let var_name = ab.var_name.clone_ref(py);
        let body = ab.body.clone_ref(py);
        drop(ab);
        // Build a Python closure that captures (body, var_name, ctx).
        return make_closure(py, body, var_name, ctx);
    }

    if let Ok(app) = bound.downcast::<Application>() {
        let app = app.borrow();
        let fun = app.fun.clone_ref(py);
        let arg = app.arg.clone_ref(py);
        drop(app);
        let f = eval_inner(py, fun.clone_ref(py), Py::new(py, clone_ctx(py, &ctx))?)?;
        let argv = eval_inner(py, arg, Py::new(py, clone_ctx(py, &ctx))?)?;
        let result: PyObject;
        if is_native_var(py, &f) {
            // Build python_ctx = {globals()} | {var.name: value}
            let evaluator_mod = py.import_bound("aeon.backend.evaluator")?;
            let globals = evaluator_mod.getattr("__dict__")?;
            let python_ctx = PyDict::new_bound(py);
            for (k, v) in globals.downcast::<PyDict>()?.iter() {
                python_ctx.set_item(k.str()?, v)?;
            }
            let ctx_b = ctx.borrow(py);
            for (k, v) in ctx_b.variables.bind(py).iter() {
                // key is a Name; use name.name (the bare ASCII).
                if let Ok(n) = k.downcast::<Name>() {
                    let nm = n.borrow().name.clone();
                    python_ctx.set_item(nm, v)?;
                }
            }
            drop(ctx_b);
            let argv_str: String = argv.extract(py)?;
            let builtins = py.import_bound("builtins")?;
            let eval_fn = builtins.getattr("eval")?;
            result = eval_fn.call1((argv_str, python_ctx))?.unbind();
        } else {
            result = f.call1(py, (argv.clone_ref(py),))?;
        }
        if is_native_import(py, &fun) {
            let evaluator_mod = py.import_bound("aeon.backend.evaluator")?;
            let globals = evaluator_mod.getattr("__dict__")?;
            let key: String = argv.extract(py)?;
            globals.set_item(key, result.clone_ref(py))?;
        }
        return Ok(result);
    }

    if let Ok(le) = bound.downcast::<Let>() {
        let le = le.borrow();
        let var_name = le.var_name.clone_ref(py);
        let var_value = le.var_value.clone_ref(py);
        let body = le.body.clone_ref(py);
        let mult = le.multiplicity.clone_ref(py);
        drop(le);
        if is_m0(py, &mult) {
            // Phase 4 — runtime erasure.
            let new_ctx = ctx.borrow(py).with_var(py, var_name, py.None())?;
            return eval_inner(py, body, Py::new(py, new_ctx)?);
        }
        let value = eval_inner(py, var_value, Py::new(py, clone_ctx(py, &ctx))?)?;
        let new_ctx = ctx.borrow(py).with_var(py, var_name, value)?;
        return eval_inner(py, body, Py::new(py, new_ctx)?);
    }

    if let Ok(rc) = bound.downcast::<Rec>() {
        let rc = rc.borrow();
        let var_name = rc.var_name.clone_ref(py);
        let var_value = rc.var_value.clone_ref(py);
        let body = rc.body.clone_ref(py);
        let mult = rc.multiplicity.clone_ref(py);
        drop(rc);
        if is_m0(py, &mult) {
            let new_ctx = ctx.borrow(py).with_var(py, var_name, py.None())?;
            return eval_inner(py, body, Py::new(py, new_ctx)?);
        }

        // LLVM fast path: look up `var_name` in `ctx.metadata` for an "llvm"
        // flag. The Python original wraps this in a bare `try/except
        // Exception:` — the swallow covers both `get_curried_function`
        // failures *and* runtime IR-parse failures triggered when the
        // returned curry is actually invoked from `body`. Mirror that here.
        let llvm_value = try_llvm_path(py, &ctx, &var_name).unwrap_or(None);
        if let Some(v) = llvm_value {
            let new_ctx = ctx.borrow(py).with_var(py, var_name.clone_ref(py), v)?;
            let attempt = eval_inner(py, body.clone_ref(py), Py::new(py, new_ctx)?);
            match attempt {
                Ok(r) => return Ok(r),
                Err(_) => {
                    // Fall through to the Python-closure path below — the
                    // LLVM-compiled function failed to invoke.
                }
            }
        }

        // If var_value is an Abstraction, build a self-referential closure;
        // otherwise eval normally.
        let value = if var_value.bind(py).is_instance_of::<Abstraction>() {
            make_rec_closure(py, var_value, var_name.clone_ref(py), ctx.clone_ref(py))?
        } else {
            eval_inner(py, var_value, Py::new(py, clone_ctx(py, &ctx))?)?
        };
        let new_ctx = ctx.borrow(py).with_var(py, var_name, value)?;
        return eval_inner(py, body, Py::new(py, new_ctx)?);
    }

    if let Ok(ife) = bound.downcast::<If>() {
        let ife = ife.borrow();
        let cond = ife.cond.clone_ref(py);
        let then = ife.then.clone_ref(py);
        let otherwise = ife.otherwise.clone_ref(py);
        drop(ife);
        let c = eval_inner(py, cond, Py::new(py, clone_ctx(py, &ctx))?)?;
        let truthy: bool = c.bind(py).is_truthy()?;
        if truthy {
            return eval_inner(py, then, ctx);
        }
        return eval_inner(py, otherwise, ctx);
    }

    if let Ok(an) = bound.downcast::<Annotation>() {
        let expr = an.borrow().expr.clone_ref(py);
        return eval_inner(py, expr, ctx);
    }

    if let Ok(hole) = bound.downcast::<Hole>() {
        let name = hole.borrow().name.clone_ref(py);
        drop(hole);
        let ctx_b = ctx.borrow(py);
        let vars = ctx_b.variables.bind(py);
        let mut names: Vec<String> = Vec::new();
        for (k, _) in vars.iter() {
            if let Ok(n) = k.downcast::<Name>() {
                names.push(n.borrow().name.clone());
            }
        }
        println!("Context ({})", names.join(", "));
        let builtins = py.import_bound("builtins")?;
        let prompt = format!("Enter value for hole {} in Python: ", name.bind(py).str()?);
        let h = builtins.getattr("input")?.call1((prompt,))?;
        let python_ctx = PyDict::new_bound(py);
        for (k, v) in vars.iter() {
            if let Ok(n) = k.downcast::<Name>() {
                python_ctx.set_item(n.borrow().name.clone(), v)?;
            }
        }
        drop(ctx_b);
        let eval_fn = builtins.getattr("eval")?;
        return Ok(eval_fn.call1((h, python_ctx))?.unbind());
    }

    if let Ok(ta) = bound.downcast::<TypeAbstraction>() {
        let body = ta.borrow().body.clone_ref(py);
        return eval_inner(py, body, ctx);
    }
    if let Ok(ra) = bound.downcast::<RefinementAbstraction>() {
        let body = ra.borrow().body.clone_ref(py);
        return eval_inner(py, body, ctx);
    }
    if let Ok(tap) = bound.downcast::<TypeApplication>() {
        let body = tap.borrow().body.clone_ref(py);
        return eval_inner(py, body, ctx);
    }
    if let Ok(rap) = bound.downcast::<RefinementApplication>() {
        let body = rap.borrow().body.clone_ref(py);
        return eval_inner(py, body, ctx);
    }

    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unknown case {}",
        bound.repr()?.to_string()
    )))
}

fn clone_ctx(py: Python<'_>, ctx: &Py<EvaluationContext>) -> EvaluationContext {
    let c = ctx.borrow(py);
    EvaluationContext {
        variables: c.variables.clone_ref(py),
        metadata: c.metadata.as_ref().map(|m| m.clone_ref(py)),
        pipeline: c.pipeline.as_ref().map(|p| p.clone_ref(py)),
    }
}

/// Create a Python closure `lambda k: eval(body, ctx.with_var(var_name, k))`.
/// We can't construct a Python lambda from Rust, so we use a helper class
/// implemented via a pyo3 #[pyclass] with `__call__`.
fn make_closure(
    py: Python<'_>,
    body: PyObject,
    var_name: Py<Name>,
    ctx: Py<EvaluationContext>,
) -> PyResult<PyObject> {
    let closure = Py::new(
        py,
        Closure {
            body,
            var_name,
            ctx,
            self_name: None,
            self_ref: None,
        },
    )?;
    Ok(closure.into_any())
}

fn make_rec_closure(
    py: Python<'_>,
    var_value: PyObject,
    var_name: Py<Name>,
    ctx: Py<EvaluationContext>,
) -> PyResult<PyObject> {
    // var_value is Abstraction(fun.var_name, fun.body, ...). When called with
    // x, we eval(fun.body, ctx.with_var(var_name, self).with_var(fun.var_name, x))
    let ab = var_value.bind(py).downcast::<Abstraction>()?.borrow();
    let fun_var_name = ab.var_name.clone_ref(py);
    let fun_body = ab.body.clone_ref(py);
    drop(ab);
    let mut closure = Py::new(
        py,
        Closure {
            body: fun_body,
            var_name: fun_var_name,
            ctx,
            self_name: Some(var_name.clone_ref(py)),
            self_ref: None,
        },
    )?;
    // Wire up self-reference: self_ref points to the closure itself.
    {
        let c = closure.borrow_mut(py);
        let _ = c;
    }
    let self_ref: PyObject = closure.clone_ref(py).into_any();
    closure.borrow_mut(py).self_ref = Some(self_ref);
    Ok(closure.into_any())
}

#[pyclass(module = "aeon_rs")]
pub struct Closure {
    body: PyObject,
    var_name: Py<Name>,
    ctx: Py<EvaluationContext>,
    /// For self-referential `Rec` closures: name to bind the closure to itself.
    self_name: Option<Py<Name>>,
    self_ref: Option<PyObject>,
}

#[pymethods]
impl Closure {
    fn __call__(&self, py: Python<'_>, k: PyObject) -> PyResult<PyObject> {
        let mut inner = clone_ctx(py, &self.ctx);
        if let (Some(self_name), Some(self_ref)) = (&self.self_name, &self.self_ref) {
            inner = inner.with_var(py, self_name.clone_ref(py), self_ref.clone_ref(py))?;
        }
        inner = inner.with_var(py, self.var_name.clone_ref(py), k)?;
        eval_inner(py, self.body.clone_ref(py), Py::new(py, inner)?)
    }
}

fn try_llvm_path(
    py: Python<'_>,
    ctx: &Py<EvaluationContext>,
    var_name: &Py<Name>,
) -> PyResult<Option<PyObject>> {
    let cb = ctx.borrow(py);
    let pipeline = match &cb.pipeline {
        Some(p) => p.clone_ref(py),
        None => return Ok(None),
    };
    let metadata = match &cb.metadata {
        Some(m) => m.clone_ref(py),
        None => return Ok(None),
    };
    drop(cb);
    let name_str = var_name.borrow(py).name.clone();
    let mut found_llvm = false;
    let meta_d = metadata.downcast_bound::<PyDict>(py)?;
    for (k, v) in meta_d.iter() {
        let k_name: String = if let Ok(n) = k.downcast::<Name>() {
            n.borrow().name.clone()
        } else {
            k.str()?.to_string()
        };
        if k_name == name_str {
            let v_dict = v.downcast::<PyDict>()?;
            if v_dict.contains("llvm")? {
                found_llvm = true;
                break;
            }
        }
    }
    if !found_llvm {
        return Ok(None);
    }
    let result = pipeline
        .bind(py)
        .call_method1("get_curried_function", (var_name.clone_ref(py),));
    match result {
        Ok(v) if !v.is_none() => Ok(Some(v.unbind())),
        _ => Ok(None),
    }
}

#[allow(dead_code)]
fn _silence(_n: &HashMap<NameKey, i64>) {
    let _ = name_key;
}
