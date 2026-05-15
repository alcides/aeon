//! Pure (z3-free) recursive walks from aeon.verification.smt that prepare
//! constraints for the SMT solver:
//!
//!   - rename_constraint            (Constraint -> Constraint)
//!   - _specialize_liquid_term       polymorphism specialization in LiquidApps
//!   - _specialize_type              type-level specialization
//!   - _term_base_type / _specialization_name   internal helpers
//!
//! These run inside `flatten` (the generator that produces CanonicConstraints
//! for the solver). flatten itself stays in Python for now — it consumes
//! SMTContext / CanonicConstraint which are smt.py-internal dataclasses.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyTuple};

use crate::builders::{
    name_eq, new_abstraction_type, new_conjunction, new_implication, new_liquid_app,
    new_liquid_constraint, new_liquid_var, new_reflected_function_declaration,
    new_refined_type, new_refinement_polymorphism, new_type_polymorphism,
    new_uninterpreted_function_declaration,
};
use crate::liquid::{
    LiquidApp, LiquidLiteralBool, LiquidLiteralFloat, LiquidLiteralInt, LiquidLiteralString,
    LiquidVar,
};
use crate::name::Name;
use crate::substitutions::substitution_in_liquid;
use crate::types::{
    AbstractionType, RefinedType, RefinementPolymorphism, Top, TypeConstructor, TypePolymorphism,
    TypeVar,
};
use crate::vcs::{
    Conjunction, Implication, LiquidConstraint, ReflectedFunctionDeclaration,
    UninterpretedFunctionDeclaration,
};

// =========================================================================
// _specialization_name
// =========================================================================

fn specialization_name(base: &str, concrete: &[String]) -> String {
    format!("{}__spec__{}", base, concrete.join("__"))
}

// =========================================================================
// _term_base_type(t, variables) -> Option<TypeConstructor>
//
// Returns None when the term has no known base type — caller treats that
// as "non-monomorphizable", i.e. skip specialization for this argument.
// =========================================================================

fn term_base_type(
    py: Python<'_>,
    t: &Bound<'_, PyAny>,
    variables: &Bound<'_, PyDict>,
) -> PyResult<Option<PyObject>> {
    // Literal cases — construct the matching TypeConstructor on the fly.
    if t.is_instance_of::<LiquidLiteralInt>() {
        return Ok(Some(builtin_tc(py, "Int")?));
    }
    if t.is_instance_of::<LiquidLiteralFloat>() {
        return Ok(Some(builtin_tc(py, "Float")?));
    }
    if t.is_instance_of::<LiquidLiteralBool>() {
        return Ok(Some(builtin_tc(py, "Bool")?));
    }
    if t.is_instance_of::<LiquidLiteralString>() {
        return Ok(Some(builtin_tc(py, "String")?));
    }
    if let Ok(v) = t.downcast::<LiquidVar>() {
        let v = v.borrow();
        let key = v.name.borrow(py).__str__();
        if let Some(found) = variables.get_item(&key)? {
            return Ok(Some(found.unbind()));
        }
        return Ok(None);
    }
    Ok(None)
}

fn builtin_tc(py: Python<'_>, name: &str) -> PyResult<PyObject> {
    let n = Py::new(py, Name { name: name.to_string(), id: 0 })?;
    let empty = PyList::empty_bound(py).unbind();
    let loc = crate::loc::default_location(py);
    crate::builders::new_type_constructor(py, n, empty, loc)
}

// =========================================================================
// _specialize_type(ty, mapping) where mapping: dict[str, TypeConstructor]
// =========================================================================

fn specialize_type(
    py: Python<'_>,
    ty: PyObject,
    mapping: &Bound<'_, PyDict>,
) -> PyResult<PyObject> {
    let bound = ty.bind(py);

    if let Ok(tc) = bound.downcast::<TypeConstructor>() {
        let tc = tc.borrow();
        let key = tc.name.borrow(py).name.clone();
        if let Some(repl) = mapping.get_item(&key)? {
            return Ok(repl.unbind());
        }
        return Ok(ty);
    }
    if let Ok(at) = bound.downcast::<AbstractionType>() {
        let at = at.borrow();
        let svty = specialize_type(py, at.var_type.clone_ref(py), mapping)?;
        let sbody = specialize_type(py, at.type_.clone_ref(py), mapping)?;
        // The Python asserts svty is Top/TypeVar/TypeConstructor/RefinedType/AbstractionType.
        // We skip the assert — invariant on the input shape.
        return new_abstraction_type(py, at.var_name.clone_ref(py), svty, sbody, at.loc.clone_ref(py));
    }
    if let Ok(tp) = bound.downcast::<TypePolymorphism>() {
        let tp = tp.borrow();
        return specialize_type(py, tp.body.clone_ref(py), mapping);
    }
    if let Ok(rp) = bound.downcast::<RefinementPolymorphism>() {
        let rp = rp.borrow();
        return specialize_type(py, rp.body.clone_ref(py), mapping);
    }
    if let Ok(rt) = bound.downcast::<RefinedType>() {
        let rt = rt.borrow();
        let sbty = specialize_type(py, rt.type_.clone_ref(py), mapping)?;
        // Python asserts sbty is TypeConstructor or TypeVar.
        return new_refined_type(
            py,
            rt.name.clone_ref(py),
            sbty,
            rt.refinement.clone_ref(py),
            rt.loc.clone_ref(py),
        );
    }
    Ok(ty)
}

// =========================================================================
// _specialize_liquid_term — threads (functions, reflected_functions, specs).
//
// Returns (new_term, new_functions, new_reflected_functions). `specializations`
// is mutated in place (mirrors Python). `variables` is read-only.
// =========================================================================

#[pyfunction]
pub fn specialize_liquid_term<'py>(
    py: Python<'py>,
    t: PyObject,
    functions: &Bound<'py, PyDict>,
    variables: &Bound<'py, PyDict>,
    reflected_functions: &Bound<'py, PyDict>,
    specializations: &Bound<'py, PyDict>,
) -> PyResult<Bound<'py, PyTuple>> {
    let bound = t.bind(py);

    // Non-LiquidApp: return unchanged with the same dicts.
    let app = match bound.downcast::<LiquidApp>() {
        Ok(app) => app,
        Err(_) => {
            return Ok(PyTuple::new_bound(
                py,
                &[t, functions.clone().into_any().unbind(), reflected_functions.clone().into_any().unbind()],
            ));
        }
    };
    let app = app.borrow();

    // Recurse into args, threading the dicts.
    let mut cur_funcs: PyObject = functions.clone().into_any().unbind();
    let mut cur_ref: PyObject = reflected_functions.clone().into_any().unbind();
    let nargs = PyList::empty_bound(py);
    let args = app.args.bind(py);
    for i in 0..args.len() {
        let arg = args.get_item(i)?;
        let tup = specialize_liquid_term(
            py,
            arg.into(),
            cur_funcs.downcast_bound::<PyDict>(py)?,
            variables,
            cur_ref.downcast_bound::<PyDict>(py)?,
            specializations,
        )?;
        let sa: PyObject = tup.get_item(0)?.into();
        cur_funcs = tup.get_item(1)?.into();
        cur_ref = tup.get_item(2)?.into();
        nargs.append(sa)?;
    }

    let fname = app.fun.borrow(py).__str__();
    let cur_funcs_dict = cur_funcs.downcast_bound::<PyDict>(py)?;
    let fty_opt = cur_funcs_dict.get_item(&fname)?;
    let fty = match fty_opt {
        Some(v) => v,
        None => {
            // No function entry — rebuild the LiquidApp with specialized args.
            let new_app =
                new_liquid_app(py, app.fun.clone_ref(py), nargs.unbind(), app.loc.clone_ref(py))?;
            return Ok(PyTuple::new_bound(py, &[new_app, cur_funcs, cur_ref]));
        }
    };

    // Walk the function's curried abstraction spine, collecting a
    // type-variable substitution map from each arg's base type.
    let subst = PyDict::new_bound(py);
    let mut cur = fty.clone();
    for i in 0..nargs.len() {
        let arg = nargs.get_item(i)?;
        let cur_at = match cur.downcast::<AbstractionType>() {
            Ok(at) => at,
            Err(_) => break,
        };
        let actual = term_base_type(py, &arg, variables)?;
        let expected = {
            let at_b = cur_at.borrow();
            at_b.var_type.clone_ref(py)
        };
        if let Some(actual_ty) = actual.as_ref() {
            // Is `expected` a lowercase-named TypeConstructor not in the builtin
            // set? Then `expected.name.name` becomes a substitution key.
            let exp_bound = expected.bind(py);
            if let Ok(tc) = exp_bound.downcast::<TypeConstructor>() {
                let tc_borrow = tc.borrow();
                let exp_name = tc_borrow.name.borrow(py).name.clone();
                let starts_lower = exp_name
                    .chars()
                    .next()
                    .map(|c| c.is_lowercase())
                    .unwrap_or(false);
                let is_builtin = matches!(
                    exp_name.as_str(),
                    "Int" | "Bool" | "Float" | "String" | "Unit" | "Top"
                );
                if starts_lower && !is_builtin {
                    subst.set_item(&exp_name, actual_ty.clone_ref(py))?;
                }
            }
        }
        let next = {
            let at_b = cur_at.borrow();
            at_b.type_.clone_ref(py)
        };
        cur = next.bind(py).clone();
    }

    if subst.len() == 0 {
        let new_app =
            new_liquid_app(py, app.fun.clone_ref(py), nargs.unbind(), app.loc.clone_ref(py))?;
        return Ok(PyTuple::new_bound(py, &[new_app, cur_funcs, cur_ref]));
    }

    // Build sorted concrete-sig tuple of value-name strings.
    let mut concrete: Vec<String> = Vec::with_capacity(subst.len());
    for (_k, v) in subst.iter() {
        // v should be a TypeConstructor with a Name
        if let Ok(tc) = v.downcast::<TypeConstructor>() {
            let tc_b = tc.borrow();
            let n = tc_b.name.borrow(py);
            concrete.push(name_to_string(&n));
        } else {
            concrete.push(v.str()?.to_string());
        }
    }
    concrete.sort();
    let skey = PyTuple::new_bound(
        py,
        &[
            fname.clone().into_py(py),
            PyTuple::new_bound(py, &concrete).into_py(py),
        ],
    );

    // Cache or freshly mint the specialization name.
    let sname = if let Some(existing) = specializations.get_item(&skey)? {
        existing.extract::<String>()?
    } else {
        let nm = specialization_name(&fname, &concrete);
        let nty = specialize_type(py, fty.clone().into(), &subst)?;
        // Assert nty is AbstractionType (Python does this).
        if !nty.bind(py).is_instance_of::<AbstractionType>() {
            return Err(pyo3::exceptions::PyAssertionError::new_err(
                "_specialize_liquid_term: specialized type is not AbstractionType",
            ));
        }
        // Build new functions dict = {**cur_funcs, sname: nty}
        let new_funcs = PyDict::new_bound(py);
        for (k, v) in cur_funcs_dict.iter() {
            new_funcs.set_item(k, v)?;
        }
        new_funcs.set_item(&nm, nty)?;
        cur_funcs = new_funcs.into_any().unbind();
        // If fname is in reflected_functions, copy it under sname.
        let cur_ref_dict = cur_ref.downcast_bound::<PyDict>(py)?;
        if let Some(rf_entry) = cur_ref_dict.get_item(&fname)? {
            let new_ref = PyDict::new_bound(py);
            for (k, v) in cur_ref_dict.iter() {
                new_ref.set_item(k, v)?;
            }
            new_ref.set_item(&nm, rf_entry)?;
            cur_ref = new_ref.into_any().unbind();
        }
        specializations.set_item(&skey, &nm)?;
        nm
    };

    // Return LiquidApp(Name(sname, 0), nargs, loc=t.loc)
    let new_fun = Py::new(py, Name { name: sname, id: 0 })?;
    let new_app = new_liquid_app(py, new_fun, nargs.unbind(), app.loc.clone_ref(py))?;
    Ok(PyTuple::new_bound(py, &[new_app, cur_funcs, cur_ref]))
}

fn name_to_string(n: &Name) -> String {
    if n.id == 0 {
        n.name.clone()
    } else if n.id == -1 {
        format!("{}?", n.name)
    } else {
        // superscript form
        let digits = ['⁰', '¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹'];
        let s = n.id.to_string();
        let mut out = String::new();
        for ch in s.chars() {
            match ch {
                '0'..='9' => out.push(digits[ch.to_digit(10).unwrap() as usize]),
                '-' => out.push('⁻'),
                _ => out.push(ch),
            }
        }
        format!("{}{}", n.name, out)
    }
}

// =========================================================================
// rename_constraint(c, old_name, new_name) — recursive Constraint walk
// =========================================================================

#[pyfunction]
pub fn rename_constraint(
    py: Python<'_>,
    c: PyObject,
    old_name: Py<Name>,
    new_name: Py<Name>,
) -> PyResult<PyObject> {
    let bound = c.bind(py);

    if let Ok(lc) = bound.downcast::<LiquidConstraint>() {
        let lc = lc.borrow();
        let new_var = new_liquid_var(
            py,
            new_name.clone_ref(py),
            crate::loc::default_location(py),
        )?;
        let nexpr = substitution_in_liquid(py, lc.expr.clone_ref(py), new_var, old_name)?;
        return new_liquid_constraint(py, nexpr, lc.loc.as_ref().map(|p| p.clone_ref(py)));
    }
    if let Ok(conj) = bound.downcast::<Conjunction>() {
        let conj = conj.borrow();
        let nc1 = rename_constraint(py, conj.c1.clone_ref(py), old_name.clone_ref(py), new_name.clone_ref(py))?;
        let nc2 = rename_constraint(py, conj.c2.clone_ref(py), old_name, new_name)?;
        return new_conjunction(py, nc1, nc2, conj.loc.as_ref().map(|p| p.clone_ref(py)));
    }
    if let Ok(imp) = bound.downcast::<Implication>() {
        let imp = imp.borrow();
        // If the bound name IS new_name, no rename (would shadow).
        if name_eq(py, &imp.name, &new_name) {
            return Ok(c);
        }
        let new_var = new_liquid_var(
            py,
            new_name.clone_ref(py),
            crate::loc::default_location(py),
        )?;
        let npred = substitution_in_liquid(py, imp.pred.clone_ref(py), new_var, old_name.clone_ref(py))?;
        let nseq = rename_constraint(py, imp.seq.clone_ref(py), old_name, new_name)?;
        return new_implication(
            py,
            imp.name.clone_ref(py),
            imp.base.clone_ref(py),
            npred,
            nseq,
            imp.loc.as_ref().map(|p| p.clone_ref(py)),
        );
    }
    if let Ok(ufd) = bound.downcast::<UninterpretedFunctionDeclaration>() {
        let ufd = ufd.borrow();
        let nseq = rename_constraint(py, ufd.seq.clone_ref(py), old_name, new_name)?;
        return new_uninterpreted_function_declaration(
            py,
            ufd.name.clone_ref(py),
            ufd.type_.clone_ref(py),
            nseq,
        );
    }
    if let Ok(rfd) = bound.downcast::<ReflectedFunctionDeclaration>() {
        let rfd = rfd.borrow();
        let new_var = new_liquid_var(
            py,
            new_name.clone_ref(py),
            crate::loc::default_location(py),
        )?;
        let nbody = substitution_in_liquid(py, rfd.body.clone_ref(py), new_var, old_name.clone_ref(py))?;
        // params: substitute old → new in each
        let params = rfd.params.bind(py);
        let new_params = PyTuple::new_bound(py, {
            let mut v: Vec<PyObject> = Vec::with_capacity(params.len());
            for i in 0..params.len() {
                let p: Py<Name> = params.get_item(i)?.extract()?;
                if name_eq(py, &p, &old_name) {
                    v.push(new_name.clone_ref(py).into_any());
                } else {
                    v.push(p.into_any());
                }
            }
            v
        });
        let nseq = rename_constraint(py, rfd.seq.clone_ref(py), old_name, new_name)?;
        return new_reflected_function_declaration(
            py,
            rfd.name.clone_ref(py),
            rfd.type_.clone_ref(py),
            new_params.unbind(),
            nbody,
            nseq,
        );
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "rename_constraint: unexpected case {}",
        bound.repr()?.to_string()
    )))
}
