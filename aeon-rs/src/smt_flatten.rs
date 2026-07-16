//! `flatten` — break a `Constraint` into a list of `CanonicConstraint`s.
//!
//! Mirrors `aeon.verification.smt.flatten`. The result is materialised
//! (`list[CanonicConstraint]`) rather than a Python generator: typical
//! VCs flatten to a handful of leaves, and a list is easier to consume
//! from both Python and Rust callers.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyTuple};

use crate::liquid::{LiquidApp, LiquidTerm, LiquidVar};
use crate::name::Name;
use crate::ple::ple_unfold_fixpoint;
use crate::smt_ctx::{empty_smt_context, CanonicConstraint, SMTContext};
use crate::smt_encode::{rename_constraint, specialize_liquid_term};
use crate::substitutions::substitution_in_liquid;
use crate::types::{
    AbstractionType, RefinementPolymorphism, TypeConstructor, TypePolymorphism, TypeVar,
};
use crate::vcs::{
    Conjunction, Implication, LiquidConstraint, ReflectedFunctionDeclaration,
    UninterpretedFunctionDeclaration,
};

/// Build `t_int` — `TypeConstructor(Name("Int", 0), [])`.
fn t_int(py: Python<'_>) -> PyResult<PyObject> {
    let n = Py::new(py, Name { name: "Int".to_string(), id: 0 })?;
    let empty = PyList::empty_bound(py).unbind();
    let loc = crate::loc::default_location(py);
    crate::builders::new_type_constructor(py, n, empty, loc)
}

/// Build a fresh `TypeConstructor(name, [])`.
fn type_constructor_no_args(py: Python<'_>, name: Py<Name>) -> PyResult<PyObject> {
    let empty = PyList::empty_bound(py).unbind();
    let loc = crate::loc::default_location(py);
    crate::builders::new_type_constructor(py, name, empty, loc)
}

/// Wraps the Rust `crate::sub::lower_constraint_type`.
fn lower_constraint_type(py: Python<'_>, t: PyObject) -> PyResult<PyObject> {
    crate::sub::lower_constraint_type(py, t)
}

/// Reduce a constraint binder `base` to the SMT-level `TypeConstructor`
/// it should be tracked as.
fn base_type_to_tc(py: Python<'_>, base: PyObject) -> PyResult<PyObject> {
    let bb = base.bind(py);
    if let Ok(tv) = bb.downcast::<TypeVar>() {
        let tv = tv.borrow();
        return type_constructor_no_args(py, tv.name.clone_ref(py));
    }
    if let Ok(tc) = bb.downcast::<TypeConstructor>() {
        let tc = tc.borrow();
        if tc.args.bind(py).len() == 0 {
            return Ok(base.clone_ref(py));
        }
        // Mangle args into a fresh sort-like TypeConstructor.
        let mut mangle = tc.name.borrow(py).__str__();
        let args = tc.args.bind(py);
        for i in 0..args.len() {
            mangle.push('_');
            mangle.push_str(&args.get_item(i)?.str()?.to_string());
        }
        let fresh = crate::name::next_fresh_id(py)?;
        let nname = Py::new(py, Name { name: mangle, id: fresh })?;
        return type_constructor_no_args(py, nname);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "{} ({}) is not a base type.",
        bb.repr()?.to_string(),
        bb.get_type().name()?,
    )))
}

/// Mirrors `aeon.verification.smt._ctx_with_curried_formals`.
fn ctx_with_curried_formals(
    py: Python<'_>,
    ctx: Py<SMTContext>,
    fun_ty: PyObject,
) -> PyResult<Py<SMTContext>> {
    let mut out = ctx;
    let mut cur = fun_ty;

    loop {
        let cur_bound = cur.bind(py);
        let Ok(at) = cur_bound.downcast::<AbstractionType>() else {
            break;
        };
        let at = at.borrow();
        let base = lower_constraint_type(py, at.var_type.clone_ref(py))?;
        let base_bound = base.bind(py);

        let base_tc: PyObject = if base_bound.is_instance_of::<TypeVar>()
            || base_bound.is_instance_of::<TypeConstructor>()
        {
            base_type_to_tc(py, base.clone_ref(py))?
        } else if base_bound.is_instance_of::<AbstractionType>()
            || base_bound.is_instance_of::<TypePolymorphism>()
            || base_bound.is_instance_of::<RefinementPolymorphism>()
        {
            // Higher-rank arguments collapse to scalar Int tokens.
            t_int(py)?
        } else {
            return Err(pyo3::exceptions::PyAssertionError::new_err(format!(
                "{} ({}) is not a base type for curried formal.",
                base_bound.repr()?.to_string(),
                base_bound.get_type().name()?,
            )));
        };

        let next = at.type_.clone_ref(py);
        let var_name_str = at.var_name.bind(py).str()?.unbind();
        drop(at);

        // out = out.with_var(cur.var_name, base_tc)
        let new_ctx: SMTContext = {
            let out_ref = out.borrow(py);
            out_ref.with_var(py, var_name_str.bind(py).as_any(), base_tc)?
        };
        out = Py::new(py, new_ctx)?;
        cur = next;
    }

    Ok(out)
}

/// `flatten(c, ctx=None)` — return a `list[CanonicConstraint]`.
#[pyfunction]
#[pyo3(signature = (c, ctx = None))]
pub fn flatten(
    py: Python<'_>,
    c: PyObject,
    ctx: Option<Py<SMTContext>>,
) -> PyResult<Py<PyList>> {
    let initial = match ctx {
        Some(c) => c,
        None => empty_smt_context(py)?,
    };
    let out = PyList::empty_bound(py);
    flatten_into(py, c, initial, &out)?;
    Ok(out.unbind())
}

fn flatten_into(
    py: Python<'_>,
    c: PyObject,
    ctx: Py<SMTContext>,
    out: &Bound<'_, PyList>,
) -> PyResult<()> {
    let cb = c.bind(py);

    if let Ok(lc) = cb.downcast::<LiquidConstraint>() {
        let expr = lc.borrow().expr.clone_ref(py);

        // Shared specialisation dict + initial function / reflected maps.
        let specs = PyDict::new_bound(py);
        let ctx_ref = ctx.borrow(py);
        let mut nfunctions: Py<PyDict> = ctx_ref.functions.clone_ref(py);
        let mut nref: Py<PyDict> = ctx_ref.reflected_functions.clone_ref(py);
        let variables: Py<PyDict> = ctx_ref.variables.clone_ref(py);
        let premises_orig: Py<PyList> = ctx_ref.premises.clone_ref(py);
        let sorts: Py<PyList> = ctx_ref.sorts.clone_ref(py);
        drop(ctx_ref);

        // Specialise each premise, threading the function / reflected dicts.
        let mut sprem: Vec<PyObject> = Vec::new();
        let premises_b = premises_orig.bind(py);
        for i in 0..premises_b.len() {
            let p = premises_b.get_item(i)?.unbind();
            let tup = specialize_liquid_term(
                py,
                p,
                nfunctions.bind(py),
                variables.bind(py),
                nref.bind(py),
                &specs,
            )?;
            sprem.push(tup.get_item(0)?.unbind());
            nfunctions = tup.get_item(1)?.downcast_into::<PyDict>()?.unbind();
            nref = tup.get_item(2)?.downcast_into::<PyDict>()?.unbind();
        }

        let tup = specialize_liquid_term(
            py,
            expr,
            nfunctions.bind(py),
            variables.bind(py),
            nref.bind(py),
            &specs,
        )?;
        let sexpr = tup.get_item(0)?.unbind();
        nfunctions = tup.get_item(1)?.downcast_into::<PyDict>()?.unbind();
        nref = tup.get_item(2)?.downcast_into::<PyDict>()?.unbind();

        // premise = [ple_unfold_fixpoint(p, nref) for p in sprem]
        let premise = PyList::empty_bound(py);
        for sp in sprem {
            let up = ple_unfold_fixpoint(py, sp, nref.bind(py), 256)?;
            premise.append(up)?;
        }

        let out_ctx = SMTContext {
            sorts,
            functions: nfunctions,
            variables,
            premises: premise.unbind(),
            reflected_functions: nref.clone_ref(py),
        };
        let out_ctx_py = Py::new(py, out_ctx)?;
        let unfolded_concl = ple_unfold_fixpoint(py, sexpr, nref.bind(py), 256)?;
        let cc = Py::new(
            py,
            CanonicConstraint::py_new(py, &out_ctx_py.borrow(py), unfolded_concl)?,
        )?;
        out.append(cc)?;
        return Ok(());
    }

    if let Ok(conj) = cb.downcast::<Conjunction>() {
        let conj = conj.borrow();
        let c1 = conj.c1.clone_ref(py);
        let c2 = conj.c2.clone_ref(py);
        drop(conj);
        flatten_into(py, c1, clone_ctx(py, &ctx)?, out)?;
        flatten_into(py, c2, ctx, out)?;
        return Ok(());
    }

    if let Ok(imp) = cb.downcast::<Implication>() {
        let imp = imp.borrow();
        let oname = imp.name.clone_ref(py);
        let base = imp.base.clone_ref(py);
        let pred = imp.pred.clone_ref(py);
        let seq = imp.seq.clone_ref(py);
        drop(imp);

        // name = Name(oname.name, fresh())
        let fresh_id = crate::name::next_fresh_id(py)?;
        let oname_str = oname.borrow(py).name.clone();
        let name = Py::new(py, Name { name: oname_str, id: fresh_id })?;

        // pred = substitution_in_liquid(pred, LiquidVar(name), oname)
        let loc = crate::loc::default_location(py);
        let var: PyObject = Py::new(
            py,
            (
                LiquidVar { name: name.clone_ref(py), loc },
                LiquidTerm,
            ),
        )?
        .into_any();
        let pred = substitution_in_liquid(py, pred, var, oname.clone_ref(py))?;
        // seq = rename_constraint(seq, oname, name)
        let seq = rename_constraint(py, seq, oname, name.clone_ref(py))?;

        let base_tc = base_type_to_tc(py, base)?;
        let name_str = name.bind(py).str()?.unbind();
        let after_var = ctx.borrow(py).with_var(py, name_str.bind(py).as_any(), base_tc)?;
        let new_ctx = after_var.with_premise(py, pred)?;
        let new_ctx_py = Py::new(py, new_ctx)?;
        flatten_into(py, seq, new_ctx_py, out)?;
        return Ok(());
    }

    if let Ok(ufd) = cb.downcast::<UninterpretedFunctionDeclaration>() {
        let ufd = ufd.borrow();
        let name = ufd.name.clone_ref(py);
        let ty = ufd.type_.clone_ref(py);
        let seq = ufd.seq.clone_ref(py);
        drop(ufd);

        let nctx = ctx_with_curried_formals(py, ctx, ty.clone_ref(py))?;
        let name_str = name.bind(py).str()?.unbind();
        let after_fn = nctx.borrow(py).with_function(py, name_str.bind(py).as_any(), ty)?;
        let after_fn_py = Py::new(py, after_fn)?;
        flatten_into(py, seq, after_fn_py, out)?;
        return Ok(());
    }

    if let Ok(rfd) = cb.downcast::<ReflectedFunctionDeclaration>() {
        let rfd = rfd.borrow();
        let name = rfd.name.clone_ref(py);
        let ty = rfd.type_.clone_ref(py);
        let params = rfd.params.clone_ref(py);
        let body = rfd.body.clone_ref(py);
        let seq = rfd.seq.clone_ref(py);
        drop(rfd);

        let nctx = ctx_with_curried_formals(py, ctx, ty.clone_ref(py))?;
        let name_str = name.bind(py).str()?.unbind();
        let after_fn = nctx.borrow(py).with_function(py, name_str.bind(py).as_any(), ty)?;
        let after_fn_py = Py::new(py, after_fn)?;
        let after_ref = after_fn_py.borrow(py).with_reflected_function(
            py,
            name_str.bind(py).as_any(),
            params.clone_ref(py).into_any(),
            body.clone_ref(py),
        )?;
        let after_ref_py = Py::new(py, after_ref)?;

        // app = LiquidApp(name, [LiquidVar(p) for p in params])
        let loc = crate::loc::default_location(py);
        let app_args = PyList::empty_bound(py);
        let params_b = params.bind(py);
        for i in 0..params_b.len() {
            let p_item = params_b.get_item(i)?;
            let p = p_item.downcast::<Name>()?.clone().unbind();
            let v: PyObject = Py::new(
                py,
                (
                    LiquidVar { name: p, loc: loc.clone_ref(py) },
                    LiquidTerm,
                ),
            )?
            .into_any();
            app_args.append(v)?;
        }
        let app: PyObject = Py::new(
            py,
            (
                LiquidApp {
                    fun: name.clone_ref(py),
                    args: app_args.unbind(),
                    loc: loc.clone_ref(py),
                },
                LiquidTerm,
            ),
        )?
        .into_any();

        // eq = LiquidApp(Name("==", 0), [app, body])
        let eq_name = Py::new(py, Name { name: "==".to_string(), id: 0 })?;
        let eq_args = PyList::new_bound(py, &[app, body]).unbind();
        let eq: PyObject = Py::new(
            py,
            (
                LiquidApp { fun: eq_name, args: eq_args, loc },
                LiquidTerm,
            ),
        )?
        .into_any();

        let after_prem = after_ref_py.borrow(py).with_premise(py, eq)?;
        let after_prem_py = Py::new(py, after_prem)?;
        flatten_into(py, seq, after_prem_py, out)?;
        return Ok(());
    }

    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Cannot flatten {}",
        cb.repr()?.to_string()
    )))
}

fn clone_ctx(py: Python<'_>, ctx: &Py<SMTContext>) -> PyResult<Py<SMTContext>> {
    let r = ctx.borrow(py);
    Py::new(
        py,
        SMTContext {
            sorts: r.sorts.clone_ref(py),
            functions: r.functions.clone_ref(py),
            variables: r.variables.clone_ref(py),
            premises: r.premises.clone_ref(py),
            reflected_functions: r.reflected_functions.clone_ref(py),
        },
    )
}

#[allow(dead_code)]
fn _silence(_t: &PyTuple) {}
