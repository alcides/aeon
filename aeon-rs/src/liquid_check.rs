//! Liquid type checker — pure refinement-term type inference.
//!
//! Direct port of `aeon.typechecking.liquid`:
//!
//!   * `LiquidTypeCheckingContext` — pyclass mirroring the Python dataclass.
//!   * `lower_abstraction_type` — flatten an AbstractionType / quantifier
//!     spine into a flat list of base sorts.
//!   * `lower_context` — distil a `TypingContext` into a
//!     `LiquidTypeCheckingContext`.
//!   * `type_infer_liquid` / `check_liquid` / `typecheck_liquid` — the
//!     inference walk over LiquidTerm.

use pyo3::create_exception;
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyTuple};

create_exception!(aeon_rs, LiquidTypeCheckException, pyo3::exceptions::PyException);

use crate::builders::new_type_constructor;
use crate::liquid::{
    LiquidApp, LiquidHornApplication, LiquidLiteralBool, LiquidLiteralFloat, LiquidLiteralInt,
    LiquidLiteralString, LiquidVar,
};
use crate::name::Name;
use crate::typectx::{
    TypeBinder, TypeConstructorBinder, TypingContext, UninterpretedBinder, VariableBinder,
};
use crate::types::{
    AbstractionType, RefinedType, RefinementPolymorphism, Top, TypeConstructor, TypePolymorphism,
    TypeVar,
};

// =============================================================================
// LiquidTypeCheckingContext
// =============================================================================

#[pyclass(module = "aeon_rs")]
pub struct LiquidTypeCheckingContext {
    /// list[TypeConstructor]
    #[pyo3(get, set)]
    pub known_types: Py<PyList>,
    /// dict[Name, TypeConstructor | TypeVar]
    #[pyo3(get, set)]
    pub variables: Py<PyDict>,
    /// dict[Name, list[TypeConstructor | TypeVar]] — flattened curried sigs
    #[pyo3(get, set)]
    pub functions: Py<PyDict>,
}

#[pymethods]
impl LiquidTypeCheckingContext {
    #[new]
    pub fn py_new(known_types: Py<PyList>, variables: Py<PyDict>, functions: Py<PyDict>) -> Self {
        LiquidTypeCheckingContext { known_types, variables, functions }
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["known_types", "variables", "functions"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let kt = self.known_types.bind(py);
        let mut kt_parts: Vec<String> = Vec::with_capacity(kt.len());
        for i in 0..kt.len() {
            kt_parts.push(kt.get_item(i)?.str()?.to_string());
        }
        let mut var_parts: Vec<String> = Vec::new();
        for (k, v) in self.variables.bind(py).iter() {
            var_parts.push(format!("{}:{}", k.str()?, v.str()?));
        }
        let mut fn_parts: Vec<String> = Vec::new();
        for (k, _) in self.functions.bind(py).iter() {
            fn_parts.push(k.str()?.to_string());
        }
        Ok(format!(
            "(LiquidGamma {} | {} | {} )",
            kt_parts.join("; "),
            var_parts.join("; "),
            fn_parts.join("; ")
        ))
    }
}

// =============================================================================
// lower_abstraction_type
// =============================================================================

/// Flatten an `AbstractionType` / quantifier spine into a list of base sorts.
/// The Python signature returns `list[TypeConstructor | TypeVar]`; we mirror
/// that, going via `to_int`/`t_unit` placeholders for awkward arg shapes.
#[pyfunction]
pub fn lower_abstraction_type(py: Python<'_>, ty: PyObject) -> PyResult<Py<PyList>> {
    let args = PyList::empty_bound(py);
    let mut cur = ty;
    loop {
        let bound = cur.bind(py);

        // Top() | RefinedType(_, Top(), _)  ->  args + [t_unit]
        if bound.is_instance_of::<Top>() {
            args.append(t_unit(py)?)?;
            return Ok(args.unbind());
        }
        if let Ok(rt) = bound.downcast::<RefinedType>() {
            let inner = rt.borrow().type_.clone_ref(py);
            if inner.bind(py).is_instance_of::<Top>() {
                args.append(t_unit(py)?)?;
                return Ok(args.unbind());
            }
            // RefinedType wrapping a base type — keep walking with the inner.
            // Python falls through to `case RefinedType(_, bt, _): return args + [bt]`.
            args.append(inner)?;
            return Ok(args.unbind());
        }
        if bound.is_instance_of::<TypeVar>() {
            assert!(args.len() > 0, "lower_abstraction_type: TypeVar with no args");
            args.append(cur)?;
            return Ok(args.unbind());
        }
        if let Ok(at) = bound.downcast::<AbstractionType>() {
            let at = at.borrow();
            let var_type = at.var_type.clone_ref(py);
            let return_type = at.type_.clone_ref(py);
            drop(at);

            // Unwrap RefinedType layers on var_type / return_type.
            let aty = match var_type.bind(py).downcast::<RefinedType>() {
                Ok(rt) => rt.borrow().type_.clone_ref(py),
                Err(_) => var_type,
            };
            let rty = match return_type.bind(py).downcast::<RefinedType>() {
                Ok(rt) => rt.borrow().type_.clone_ref(py),
                Err(_) => return_type,
            };

            // Classify aty.
            let aty_b = aty.bind(py);
            if aty_b.is_instance_of::<TypeConstructor>() || aty_b.is_instance_of::<TypeVar>() {
                args.append(aty)?;
            } else if aty_b.is_instance_of::<Top>() {
                args.append(t_unit(py)?)?;
            } else {
                // Higher-order argument — collapse to Int.
                args.append(t_int(py)?)?;
            }
            cur = rty;
            continue;
        }
        if let Ok(tp) = bound.downcast::<TypePolymorphism>() {
            let body = tp.borrow().body.clone_ref(py);
            return lower_abstraction_type(py, body);
        }
        if let Ok(rp) = bound.downcast::<RefinementPolymorphism>() {
            let body = rp.borrow().body.clone_ref(py);
            return lower_abstraction_type(py, body);
        }
        if bound.is_instance_of::<TypeConstructor>() {
            args.append(cur)?;
            return Ok(args.unbind());
        }
        return Err(pyo3::exceptions::PyAssertionError::new_err(format!(
            "Unknown type {} when lowering to liquid",
            bound.repr()?.to_string()
        )));
    }
}

fn t_unit(py: Python<'_>) -> PyResult<PyObject> {
    base_tc(py, "Unit")
}
fn t_int(py: Python<'_>) -> PyResult<PyObject> {
    base_tc(py, "Int")
}
fn t_bool(py: Python<'_>) -> PyResult<PyObject> {
    base_tc(py, "Bool")
}
fn t_float(py: Python<'_>) -> PyResult<PyObject> {
    base_tc(py, "Float")
}
fn t_string(py: Python<'_>) -> PyResult<PyObject> {
    base_tc(py, "String")
}

fn base_tc(py: Python<'_>, name: &str) -> PyResult<PyObject> {
    let n = Py::new(py, Name { name: name.to_string(), id: 0 })?;
    let empty = PyList::empty_bound(py).unbind();
    new_type_constructor(py, n, empty, crate::loc::default_location(py))
}

// =============================================================================
// lower_context
// =============================================================================

const NATIVE_TYPES: &[&str] = &[
    "Unit", "Bool", "Int", "Float", "String", "Set", "Tensor", "GpuConfig",
];

#[pyfunction]
pub fn lower_context(py: Python<'_>, ctx: &Bound<'_, TypingContext>) -> PyResult<LiquidTypeCheckingContext> {
    let mut known_type_names: Vec<Py<Name>> = Vec::new();
    for nm in NATIVE_TYPES {
        known_type_names.push(Py::new(
            py,
            Name { name: nm.to_string(), id: 0 },
        )?);
    }
    let variables = PyDict::new_bound(py);
    let functions = PyDict::new_bound(py);

    let ctx_b = ctx.borrow();
    let entries = ctx_b.entries.clone_ref(py);
    drop(ctx_b);
    let entries_b = entries.bind(py);

    // Iterate entries in reverse (newest first).
    for i in (0..entries_b.len()).rev() {
        let entry = entries_b.get_item(i)?;

        if let Ok(vb) = entry.downcast::<VariableBinder>() {
            let vb = vb.borrow();
            let name = vb.name.clone_ref(py);
            let ty = vb.type_.clone_ref(py);
            drop(vb);
            handle_variable_binder(py, name, ty, &mut known_type_names, &variables, &functions)?;
            continue;
        }
        if let Ok(tb) = entry.downcast::<TypeBinder>() {
            let tb = tb.borrow();
            known_type_names.push(tb.type_name.clone_ref(py));
            continue;
        }
        if let Ok(ub) = entry.downcast::<UninterpretedBinder>() {
            let ub = ub.borrow();
            let name = ub.name.clone_ref(py);
            let ty = ub.type_.clone_ref(py);
            drop(ub);
            // UninterpretedBinder(_, AbstractionType(...))  |  with TypePoly wrap.
            let ty_b = ty.bind(py);
            if ty_b.is_instance_of::<AbstractionType>() {
                let sig = lower_abstraction_type(py, ty)?;
                functions.set_item(name, sig)?;
            } else if let Ok(tp) = ty_b.downcast::<TypePolymorphism>() {
                let body = tp.borrow().body.clone_ref(py);
                if body.bind(py).is_instance_of::<AbstractionType>() {
                    let sig = lower_abstraction_type(py, ty)?;
                    functions.set_item(name, sig)?;
                }
            }
            continue;
        }
        if entry.downcast::<TypeConstructorBinder>().is_ok() {
            continue;
        }
        return Err(pyo3::exceptions::PyAssertionError::new_err(format!(
            "Unknown context type {}",
            entry.repr()?.to_string()
        )));
    }

    // Build the known_types list (TypeConstructor(n) for each name).
    let known_types = PyList::empty_bound(py);
    for n in known_type_names {
        let empty = PyList::empty_bound(py).unbind();
        let tc = new_type_constructor(py, n, empty, crate::loc::default_location(py))?;
        known_types.append(tc)?;
    }

    Ok(LiquidTypeCheckingContext {
        known_types: known_types.unbind(),
        variables: variables.unbind(),
        functions: functions.unbind(),
    })
}

fn handle_variable_binder(
    py: Python<'_>,
    name: Py<Name>,
    ty: PyObject,
    known_type_names: &mut Vec<Py<Name>>,
    variables: &Bound<'_, PyDict>,
    functions: &Bound<'_, PyDict>,
) -> PyResult<()> {
    let ty_b = ty.bind(py);
    if ty_b.is_instance_of::<TypeConstructor>() {
        variables.set_item(name, ty)?;
        return Ok(());
    }
    if let Ok(tv) = ty_b.downcast::<TypeVar>() {
        let tv_name = tv.borrow().name.clone_ref(py);
        known_type_names.push(tv_name.clone_ref(py));
        let empty = PyList::empty_bound(py).unbind();
        let tv_obj = Py::new(
            py,
            (
                TypeVar { name: tv_name, loc: crate::loc::default_location(py) },
                crate::types::Type,
            ),
        )?
        .into_any();
        let _ = empty;
        variables.set_item(name, tv_obj)?;
        return Ok(());
    }
    if ty_b.is_instance_of::<TypePolymorphism>() || ty_b.is_instance_of::<RefinementPolymorphism>() {
        let sig = lower_abstraction_type(py, ty)?;
        functions.set_item(name, sig)?;
        return Ok(());
    }
    if ty_b.is_instance_of::<AbstractionType>() {
        let sig = lower_abstraction_type(py, ty)?;
        functions.set_item(name, sig)?;
        return Ok(());
    }
    if let Ok(rt) = ty_b.downcast::<RefinedType>() {
        let inner = rt.borrow().type_.clone_ref(py);
        let inner_b = inner.bind(py);
        if inner_b.is_instance_of::<TypeConstructor>() {
            variables.set_item(name, inner)?;
            return Ok(());
        }
        if let Ok(tv) = inner_b.downcast::<TypeVar>() {
            let tv_name = tv.borrow().name.clone_ref(py);
            known_type_names.push(tv_name);
            variables.set_item(name, inner)?;
            return Ok(());
        }
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unknown context type for variable {} : {}",
        name.bind(py).str()?,
        ty_b.repr()?.to_string()
    )))
}

// =============================================================================
// type_infer_liquid / check_liquid
// =============================================================================

#[pyfunction]
pub fn type_infer_liquid(
    py: Python<'_>,
    ctx: &Bound<'_, LiquidTypeCheckingContext>,
    liq: PyObject,
) -> PyResult<PyObject> {
    let bound = liq.bind(py);
    if bound.is_instance_of::<LiquidLiteralBool>() {
        return t_bool(py);
    }
    if bound.is_instance_of::<LiquidLiteralInt>() {
        return t_int(py);
    }
    if bound.is_instance_of::<LiquidLiteralFloat>() {
        return t_float(py);
    }
    if bound.is_instance_of::<LiquidLiteralString>() {
        return t_string(py);
    }
    if let Ok(v) = bound.downcast::<LiquidVar>() {
        let v = v.borrow();
        let nm = v.name.clone_ref(py);
        drop(v);
        let ctx_b = ctx.borrow();
        let variables = ctx_b.variables.bind(py);
        if let Some(entry) = variables.get_item(nm.clone_ref(py))? {
            // Match TypeConstructor (any args) or TypeVar.
            if entry.is_instance_of::<TypeConstructor>() || entry.is_instance_of::<TypeVar>() {
                return Ok(entry.unbind());
            }
            return Err(LiquidTypeCheckException::new_err(format!(
                "Could not find type for LiquidVar {}",
                nm.bind(py).str()?
            )));
        }
        return Err(LiquidTypeCheckException::new_err(format!(
            "Variable {} not in context in {:?}.",
            nm.bind(py).str()?,
            ctx_b.__repr__(py)?
        )));
    }
    if bound.is_instance_of::<LiquidHornApplication>() {
        return t_bool(py);
    }
    if let Ok(app) = bound.downcast::<LiquidApp>() {
        let app = app.borrow();
        let fun = app.fun.clone_ref(py);
        let args = app.args.clone_ref(py);
        let loc = app.loc.clone_ref(py);
        drop(app);
        drop(loc);
        let ctx_b = ctx.borrow();
        let functions = ctx_b.functions.bind(py);
        let Some(ftype_obj) = functions.get_item(fun.clone_ref(py))? else {
            return Err(LiquidTypeCheckException::new_err(format!(
                "Function {} not in context in {} ({:?}).",
                fun.bind(py).str()?,
                liq.bind(py).repr()?,
                ctx_b.functions.bind(py).str()?
            )));
        };
        let ftype = ftype_obj.downcast::<PyList>()?.clone();
        let ftype_len = ftype.len();
        drop(ctx_b);

        let args_b = args.bind(py);
        if ftype_len != args_b.len() + 1 {
            return Err(LiquidTypeCheckException::new_err(format!(
                "Function application {} needs {} arguments, but was passed {}.",
                liq.bind(py).repr()?,
                ftype_len - 1,
                args_b.len()
            )));
        }

        // equalities: TypeVar name -> resolved TypeConstructor | TypeVar
        let equalities = PyDict::new_bound(py);
        let mut type_of_args: Vec<PyObject> = Vec::with_capacity(args_b.len());
        for i in 0..args_b.len() {
            let arg = args_b.get_item(i)?.unbind();
            let k = type_infer_liquid(py, ctx, arg.clone_ref(py))?;
            type_of_args.push(k.clone_ref(py));
            let exp_t = ftype.get_item(i)?.unbind();
            unify(py, &k, &exp_t, &equalities, &arg, &liq)?;
        }

        // Built-in operator type guards.
        check_op_guard(py, &fun, &type_of_args)?;

        // Resolve the result type through equalities.
        let result = ftype.get_item(ftype_len - 1)?.unbind();
        return resolve_type(py, result, &equalities);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Constructed {} not supported.",
        bound.repr()?.to_string()
    )))
}

fn resolve_type(py: Python<'_>, ty: PyObject, equalities: &Bound<'_, PyDict>) -> PyResult<PyObject> {
    let bound = ty.bind(py);
    if bound.is_instance_of::<TypeConstructor>() {
        return Ok(ty);
    }
    if let Ok(tv) = bound.downcast::<TypeVar>() {
        let nm = tv.borrow().name.clone_ref(py);
        if let Some(repl) = equalities.get_item(nm)? {
            return resolve_type(py, repl.unbind(), equalities);
        }
        return Ok(ty);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err("unknown stuff"))
}

fn unify(
    py: Python<'_>,
    k: &PyObject,
    exp_t: &PyObject,
    equalities: &Bound<'_, PyDict>,
    arg: &PyObject,
    liq: &PyObject,
) -> PyResult<()> {
    let kb = k.bind(py);
    let eb = exp_t.bind(py);
    // (TypeConstructor(t), TypeConstructor(e))
    if let (Ok(kc), Ok(ec)) = (kb.downcast::<TypeConstructor>(), eb.downcast::<TypeConstructor>()) {
        let kn = kc.borrow();
        let en = ec.borrow();
        let knn = kn.name.borrow(py);
        let enn = en.name.borrow(py);
        if knn.name != enn.name || knn.id != enn.id {
            return Err(LiquidTypeCheckException::new_err(format!(
                "Argument {} in {} is expected to be of type {}, but {} was found instead.",
                arg.bind(py).repr()?,
                liq.bind(py).repr()?,
                exp_t.bind(py).str()?,
                k.bind(py).str()?
            )));
        }
        return Ok(());
    }
    // (TypeConstructor, TypeVar(name)) — record / check equality
    if let (Ok(_kc), Ok(etv)) = (kb.downcast::<TypeConstructor>(), eb.downcast::<TypeVar>()) {
        let tv_name = etv.borrow().name.clone_ref(py);
        let resolved = resolve_type(py, k.clone_ref(py), equalities)?;
        if !equalities.contains(tv_name.clone_ref(py))? {
            equalities.set_item(tv_name, resolved)?;
        } else {
            // already in; verify match
            let already = resolve_type(
                py,
                Py::new(
                    py,
                    (
                        TypeVar {
                            name: tv_name,
                            loc: crate::loc::default_location(py),
                        },
                        crate::types::Type,
                    ),
                )?
                .into_any(),
                equalities,
            )?;
            if !already.bind(py).eq(k.bind(py))? {
                return Err(LiquidTypeCheckException::new_err(format!(
                    "Argument {} in {} is expected to be of type {} ({}), but {} was found instead.",
                    arg.bind(py).repr()?,
                    liq.bind(py).repr()?,
                    exp_t.bind(py).str()?,
                    already.bind(py).str()?,
                    k.bind(py).str()?
                )));
            }
        }
        return Ok(());
    }
    // (TypeVar(t), TypeVar(name))
    if let (Ok(_ktv), Ok(etv)) = (kb.downcast::<TypeVar>(), eb.downcast::<TypeVar>()) {
        let tv_name = etv.borrow().name.clone_ref(py);
        let resolved = resolve_type(py, k.clone_ref(py), equalities)?;
        if !equalities.contains(tv_name.clone_ref(py))? {
            equalities.set_item(tv_name, resolved)?;
        } else {
            let already = resolve_type(
                py,
                Py::new(
                    py,
                    (
                        TypeVar {
                            name: tv_name,
                            loc: crate::loc::default_location(py),
                        },
                        crate::types::Type,
                    ),
                )?
                .into_any(),
                equalities,
            )?;
            if !already.bind(py).eq(k.bind(py))? {
                return Err(LiquidTypeCheckException::new_err(format!(
                    "Argument {} in {} is expected to be of type {}, but {} was found instead.",
                    arg.bind(py).repr()?,
                    liq.bind(py).repr()?,
                    exp_t.bind(py).str()?,
                    k.bind(py).str()?
                )));
            }
        }
        return Ok(());
    }
    Err(LiquidTypeCheckException::new_err(format!(
        "Could not unify {} and {} in {}.",
        kb.repr()?.to_string(),
        eb.repr()?.to_string(),
        liq.bind(py).repr()?.to_string()
    )))
}

fn check_op_guard(
    py: Python<'_>,
    fun: &Py<Name>,
    type_of_args: &[PyObject],
) -> PyResult<()> {
    if type_of_args.is_empty() {
        return Ok(());
    }
    let fun_name = fun.borrow(py).name.clone();
    let first = &type_of_args[0];
    let first_b = first.bind(py);
    let is_typevar = first_b.is_instance_of::<TypeVar>();

    let is_base_in = |names: &[&str]| -> PyResult<bool> {
        if let Ok(tc) = first_b.downcast::<TypeConstructor>() {
            let n = tc.borrow().name.borrow(py).name.clone();
            return Ok(names.contains(&n.as_str()));
        }
        Ok(false)
    };

    if matches!(fun_name.as_str(), "<" | "<=" | ">" | ">=") {
        if !is_base_in(&["Float", "Int"])? && !is_typevar {
            return Err(LiquidTypeCheckException::new_err(format!(
                "Function {} only applies to Floats or Ints.",
                fun_name
            )));
        }
    } else if matches!(fun_name.as_str(), "==" | "!=") {
        if !is_typevar
            && !is_base_in(&["Unit", "Bool", "Float", "Int", "String", "Set"])?
            && !first_b.is_instance_of::<TypeConstructor>()
        {
            return Err(LiquidTypeCheckException::new_err(format!(
                "Function {} only applies to built-in types.",
                fun_name
            )));
        }
    } else if matches!(fun_name.as_str(), "+" | "-" | "*" | "/") {
        if !is_typevar && !is_base_in(&["Float", "Int"])? {
            return Err(LiquidTypeCheckException::new_err(format!(
                "Function {} only applies to Floats or Ints.",
                fun_name
            )));
        }
    }
    Ok(())
}

#[pyfunction]
pub fn check_liquid(
    py: Python<'_>,
    ctx: &Bound<'_, LiquidTypeCheckingContext>,
    liq: PyObject,
    exp: PyObject,
) -> PyResult<bool> {
    match type_infer_liquid(py, ctx, liq) {
        Ok(t) => Ok(t.bind(py).eq(exp.bind(py))?),
        Err(_) => Ok(false),
    }
}

#[pyfunction]
pub fn typecheck_liquid(
    py: Python<'_>,
    ctx: &Bound<'_, TypingContext>,
    liq: PyObject,
) -> PyResult<PyObject> {
    let lctx = lower_context(py, ctx)?;
    let lctx_py = Py::new(py, lctx)?;
    type_infer_liquid(py, lctx_py.bind(py), liq)
}
