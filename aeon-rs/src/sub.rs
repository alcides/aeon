//! Subtyping → constraint generation.
//!
//! Direct port of `aeon.verification.sub`. The `TypingContext` argument is
//! threaded through recursive calls but never read by the subtyping logic
//! itself, so we accept it as an opaque `PyObject`.

use pyo3::prelude::*;
use pyo3::types::PyTuple;

use crate::builders::{
    new_abstraction_type_mult, new_conjunction, new_implication, new_liquid_constraint,
    new_liquid_literal_bool, new_liquid_var, new_refined_type, new_type_constructor,
    new_uninterpreted_function_declaration,
};
use crate::liquefy::substitution_in_type;
use crate::name::Name;
use crate::substitutions::substitution_in_liquid;
use crate::types::{
    AbstractionType, ExistentialType, RefinedType, RefinementPolymorphism, Top, TypeConstructor,
    TypePolymorphism, TypeVar,
};

/// `Option<PyObject>` doesn't implement `Clone` — clone manually under the
/// GIL when we need to pass `loc` down multiple call sites.
fn loc_clone(py: Python<'_>, loc: &Option<PyObject>) -> Option<PyObject> {
    loc.as_ref().map(|o| o.clone_ref(py))
}

// =============================================================================
// Module-level constants — built lazily because they need the Python GIL.
// =============================================================================

fn ctrue(py: Python<'_>) -> PyResult<PyObject> {
    let lb = new_liquid_literal_bool(py, true, crate::loc::default_location(py))?;
    new_liquid_constraint(py, lb, None)
}

fn cfalse(py: Python<'_>) -> PyResult<PyObject> {
    let lb = new_liquid_literal_bool(py, false, crate::loc::default_location(py))?;
    new_liquid_constraint(py, lb, None)
}

// =============================================================================
// ensure_refined — wrap bare base types in a trivial RefinedType.
// =============================================================================

#[pyfunction]
pub fn ensure_refined(py: Python<'_>, t: PyObject) -> PyResult<PyObject> {
    let bound = t.bind(py);
    if bound.is_instance_of::<RefinedType>() {
        return Ok(t);
    }
    if let Ok(tv) = bound.downcast::<TypeVar>() {
        let tv = tv.borrow();
        let inner_name = tv.name.borrow(py).name.clone();
        let fresh_id = crate::name::next_fresh_id(py)?;
        let singleton = Py::new(
            py,
            Name {
                name: format!("singleton_{}", inner_name),
                id: fresh_id,
            },
        )?;
        let lb = new_liquid_literal_bool(py, true, crate::loc::default_location(py))?;
        return new_refined_type(py, singleton, t, lb, crate::loc::default_location(py));
    }
    if let Ok(tc) = bound.downcast::<TypeConstructor>() {
        let tc = tc.borrow();
        let inner_name = tc.name.borrow(py).name.clone();
        let fresh_id = crate::name::next_fresh_id(py)?;
        let singleton = Py::new(
            py,
            Name {
                name: format!("singleton_{}", inner_name),
                id: fresh_id,
            },
        )?;
        let lb = new_liquid_literal_bool(py, true, crate::loc::default_location(py))?;
        return new_refined_type(py, singleton, t, lb, crate::loc::default_location(py));
    }
    Ok(t)
}

// =============================================================================
// is_first_order_function — true if every var_type along the spine is a base
// type / type-var / polymorphism (no nested AbstractionType arguments).
// =============================================================================

#[pyfunction]
pub fn is_first_order_function(py: Python<'_>, at: PyObject) -> PyResult<bool> {
    let mut current = at;

    // Peel polymorphism wrappers.
    loop {
        let bound = current.bind(py);
        if let Ok(tp) = bound.downcast::<TypePolymorphism>() {
            let body = tp.borrow().body.clone_ref(py);
            current = body;
            continue;
        }
        if let Ok(rp) = bound.downcast::<RefinementPolymorphism>() {
            let body = rp.borrow().body.clone_ref(py);
            current = body;
            continue;
        }
        break;
    }

    // Walk the AbstractionType spine.
    loop {
        let bound = current.bind(py);
        let Ok(at) = bound.downcast::<AbstractionType>() else {
            break;
        };
        let at = at.borrow();
        let vt = at.var_type.bind(py);
        if vt.is_instance_of::<AbstractionType>() {
            return Ok(false);
        }
        // Anything else (Top, RefinedType, TypeVar, TypeConstructor, polys) — OK.
        let next = at.type_.clone_ref(py);
        drop(at);
        current = next;
    }
    Ok(true)
}

// =============================================================================
// lower_constraint_type — strip away refinements / quantifiers; map Top to
// the canonical `t_unit` TypeConstructor.
// =============================================================================

#[pyfunction]
pub fn lower_constraint_type(py: Python<'_>, ttype: PyObject) -> PyResult<PyObject> {
    let bound = ttype.bind(py);
    if let Ok(tv) = bound.downcast::<TypeVar>() {
        let tv = tv.borrow();
        let empty = pyo3::types::PyList::empty_bound(py).unbind();
        return new_type_constructor(
            py,
            tv.name.clone_ref(py),
            empty,
            crate::loc::default_location(py),
        );
    }
    if bound.is_instance_of::<Top>() {
        // t_unit: TypeConstructor(Name("Unit", 0), [])
        let n = Py::new(py, Name { name: "Unit".to_string(), id: 0 })?;
        let empty = pyo3::types::PyList::empty_bound(py).unbind();
        return new_type_constructor(py, n, empty, crate::loc::default_location(py));
    }
    if let Ok(at) = bound.downcast::<AbstractionType>() {
        let at = at.borrow();
        let nb = lower_constraint_type(py, at.var_type.clone_ref(py))?;
        let nr = lower_constraint_type(py, at.type_.clone_ref(py))?;
        return new_abstraction_type_mult(
            py,
            at.var_name.clone_ref(py),
            nb,
            nr,
            at.loc.clone_ref(py),
            at.multiplicity.clone_ref(py),
        );
    }
    if let Ok(tp) = bound.downcast::<TypePolymorphism>() {
        let body = tp.borrow().body.clone_ref(py);
        return lower_constraint_type(py, body);
    }
    if let Ok(rp) = bound.downcast::<RefinementPolymorphism>() {
        let body = rp.borrow().body.clone_ref(py);
        return lower_constraint_type(py, body);
    }
    if let Ok(rt) = bound.downcast::<RefinedType>() {
        let inner = rt.borrow().type_.clone_ref(py);
        return lower_constraint_type(py, inner);
    }
    if let Ok(tc) = bound.downcast::<TypeConstructor>() {
        let tc = tc.borrow();
        if tc.args.bind(py).len() > 0 {
            // Polymorphic types collapse to Top.
            let n = Py::new(py, Name { name: "Top".to_string(), id: 0 })?;
            let empty = pyo3::types::PyList::empty_bound(py).unbind();
            return new_type_constructor(py, n, empty, crate::loc::default_location(py));
        }
        // Bare type constructor — rebuild without args, keeping the name.
        let empty = pyo3::types::PyList::empty_bound(py).unbind();
        return new_type_constructor(
            py,
            tc.name.clone_ref(py),
            empty,
            crate::loc::default_location(py),
        );
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unsupport type in constraint {} ({})",
        bound.repr()?.to_string(),
        bound.get_type().name()?,
    )))
}

// =============================================================================
// implication_constraint — wrap a constraint with the right binder kind.
// =============================================================================

#[pyfunction]
#[pyo3(signature = (name, ty, c, loc = None, reflected_impl = None))]
pub fn implication_constraint(
    py: Python<'_>,
    name: Py<Name>,
    ty: PyObject,
    c: PyObject,
    loc: Option<PyObject>,
    reflected_impl: Option<PyObject>,
) -> PyResult<PyObject> {
    let bound = ty.bind(py);

    // Plain base type or unrefined wrapper.
    if bound.is_instance_of::<Top>()
        || bound.is_instance_of::<TypeVar>()
        || bound.is_instance_of::<TypeConstructor>()
    {
        let basety = lower_constraint_type(py, ty)?;
        let lb = new_liquid_literal_bool(py, true, crate::loc::default_location(py))?;
        return new_implication(py, name, basety, lb, c, loc);
    }

    if let Ok(rt) = bound.downcast::<RefinedType>() {
        let rt = rt.borrow();
        let tname = rt.name.clone_ref(py);
        let tref = rt.refinement.clone_ref(py);
        let inner_ty = rt.type_.clone_ref(py);
        drop(rt);
        // ref_subs = substitution_in_liquid(tref, LiquidVar(name), tname)
        let lv = new_liquid_var(py, name.clone_ref(py), crate::loc::default_location(py))?;
        let ref_subs = substitution_in_liquid(py, tref, lv, tname)?;
        let ltype = lower_constraint_type(py, inner_ty)?;
        return new_implication(py, name, ltype, ref_subs, c, loc);
    }

    if bound.is_instance_of::<AbstractionType>() {
        if is_first_order_function(py, ty.clone_ref(py))? {
            let absty = lower_constraint_type(py, ty)?;
            if let Some(refl) = reflected_impl {
                let refl_b = refl.bind(py);
                let params: Py<PyTuple> = refl_b.get_item(0)?.downcast::<PyTuple>()?.clone().unbind();
                let body: PyObject = refl_b.get_item(1)?.unbind();
                return crate::builders::new_reflected_function_declaration(
                    py, name, absty, params, body, c,
                );
            }
            return new_uninterpreted_function_declaration(py, name, absty, c);
        }
        return Ok(c);
    }

    // TypePolymorphism / RefinementPolymorphism — reflected only if the
    // lowered type is an AbstractionType.
    if bound.is_instance_of::<TypePolymorphism>() || bound.is_instance_of::<RefinementPolymorphism>() {
        if let Some(refl) = reflected_impl {
            let lowered = lower_constraint_type(py, ty)?;
            if lowered.bind(py).is_instance_of::<AbstractionType>() {
                let refl_b = refl.bind(py);
                let params: Py<PyTuple> = refl_b.get_item(0)?.downcast::<PyTuple>()?.clone().unbind();
                let body: PyObject = refl_b.get_item(1)?.unbind();
                return crate::builders::new_reflected_function_declaration(
                    py, name, lowered, params, body, c,
                );
            }
        }
        return Ok(c);
    }

    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "implication_constraint: unhandled type {}",
        bound.repr()?.to_string()
    )))
}

// =============================================================================
// sub — the main subtyping function.
// =============================================================================

#[pyfunction]
#[pyo3(signature = (ctx, t1, t2, loc = None))]
pub fn sub(
    py: Python<'_>,
    ctx: PyObject,
    t1: PyObject,
    t2: PyObject,
    loc: Option<PyObject>,
) -> PyResult<PyObject> {
    // t2 == Top()  =>  ctrue (any type <: Top)
    if t2.bind(py).is_instance_of::<Top>() {
        return ctrue(py);
    }

    // Existential on the subtype side: skolemise each binder.
    if let Ok(et1) = t1.bind(py).downcast::<ExistentialType>() {
        let body = et1.borrow().body.clone_ref(py);
        let binders = et1.borrow().binders.clone_ref(py);
        drop(et1);
        let mut c = sub(py, ctx.clone_ref(py), body, t2, loc_clone(py, &loc))?;
        let binders_b = binders.bind(py);
        // Wrap from innermost out.
        for i in (0..binders_b.len()).rev() {
            let tup = binders_b.get_item(i)?;
            let bn: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
            let bt: PyObject = tup.get_item(1)?.unbind();
            c = implication_constraint(py, bn, bt, c, loc_clone(py, &loc), None)?;
        }
        return Ok(c);
    }

    // Existential on the supertype side: peel and recurse on the body.
    if let Ok(et2) = t2.bind(py).downcast::<ExistentialType>() {
        let body = et2.borrow().body.clone_ref(py);
        drop(et2);
        return sub(py, ctx, t1, body, loc);
    }

    // Ensure both sides are refined and dispatch on the shape.
    let r1 = ensure_refined(py, t1.clone_ref(py))?;
    let r2 = ensure_refined(py, t2.clone_ref(py))?;
    let r1b = r1.bind(py);
    let r2b = r2.bind(py);

    // Refined <: Refined
    if let (Ok(rt1), Ok(rt2)) = (r1b.downcast::<RefinedType>(), r2b.downcast::<RefinedType>()) {
        let rt1 = rt1.borrow();
        let rt2 = rt2.borrow();

        let ty2_b = rt2.type_.bind(py);
        if ty2_b.is_instance_of::<Top>() {
            return ctrue(py);
        }
        if !rt1.type_.bind(py).eq(rt2.type_.bind(py))? {
            return cfalse(py);
        }

        let n1 = rt1.name.borrow(py);
        let n2 = rt2.name.borrow(py);
        let combined = format!("{}{}", n1.name, n2.name);
        drop(n1);
        drop(n2);
        let fresh_id = crate::name::next_fresh_id(py)?;
        let new_name = Py::new(py, Name { name: combined, id: fresh_id })?;

        let r2_inner = rt2.refinement.clone_ref(py);
        let r1_inner = rt1.refinement.clone_ref(py);
        let n1_old = rt1.name.clone_ref(py);
        let n2_old = rt2.name.clone_ref(py);
        let ty1_inner = rt1.type_.clone_ref(py);
        drop(rt1);
        drop(rt2);

        let lv = new_liquid_var(py, new_name.clone_ref(py), crate::loc::default_location(py))?;
        let r2_subbed = substitution_in_liquid(py, r2_inner, lv.clone_ref(py), n2_old)?;
        let r1_subbed = substitution_in_liquid(py, r1_inner, lv, n1_old)?;

        let lowert = lower_constraint_type(py, ty1_inner)?;
        let inner_constraint = new_liquid_constraint(py, r2_subbed, loc_clone(py, &loc))?;
        return new_implication(py, new_name, lowert, r1_subbed, inner_constraint, loc);
    }

    // ∀ on the left — only the body matters for subtyping at this level.
    if r1b.is_instance_of::<TypePolymorphism>() || r1b.is_instance_of::<RefinementPolymorphism>() {
        return ctrue(py);
    }

    // (a1:t1) -> rt1  <:  (a2:t2) -> rt2
    if let (Ok(at1), Ok(at2)) = (r1b.downcast::<AbstractionType>(), r2b.downcast::<AbstractionType>()) {
        let at1 = at1.borrow();
        let at2 = at2.borrow();

        let n1 = at1.var_name.borrow(py);
        let n2 = at2.var_name.borrow(py);
        let combined = format!("{}{}", n1.name, n2.name);
        drop(n1);
        drop(n2);
        let fresh_id = crate::name::next_fresh_id(py)?;
        let new_name = Py::new(py, Name { name: combined, id: fresh_id })?;

        let vt1 = at1.var_type.clone_ref(py);
        let vt2 = at2.var_type.clone_ref(py);
        let rt1_inner = at1.type_.clone_ref(py);
        let rt2_inner = at2.type_.clone_ref(py);
        let a1_old = at1.var_name.clone_ref(py);
        let a2_old = at2.var_name.clone_ref(py);
        drop(at1);
        drop(at2);

        // Contravariant arg subtyping.
        let c0 = sub(py, ctx.clone_ref(py), vt2.clone_ref(py), vt1, loc_clone(py, &loc))?;

        // Python uses substitution_in_type(rt, Var(name), old) — replace a Term
        // variable inside a Type, via liquefication.
        let var_new = crate::builders::new_var(py, new_name.clone_ref(py), crate::loc::default_location(py))?;
        let rt1_subbed =
            substitution_in_type(py, rt1_inner, var_new.clone_ref(py), a1_old)?;
        let rt2_subbed = substitution_in_type(py, rt2_inner, var_new, a2_old)?;

        let c1 = sub(py, ctx, rt1_subbed, rt2_subbed, loc_clone(py, &loc))?;
        let wrapped = implication_constraint(py, new_name, vt2, c1, loc, None)?;
        return new_conjunction(py, c0, wrapped, None);
    }

    // TC <: TC — invariant args.
    if let (Ok(tc1), Ok(tc2)) = (r1b.downcast::<TypeConstructor>(), r2b.downcast::<TypeConstructor>()) {
        let tc1 = tc1.borrow();
        let tc2 = tc2.borrow();
        let n1 = tc1.name.borrow(py);
        let n2 = tc2.name.borrow(py);
        if !(n1.name == n2.name && n1.id == n2.id) {
            return cfalse(py);
        }
        let a1 = tc1.args.bind(py);
        let a2 = tc2.args.bind(py);
        if a1.len() != a2.len() {
            return cfalse(py);
        }
        for i in 0..a1.len() {
            if !a1.get_item(i)?.eq(a2.get_item(i)?)? {
                return cfalse(py);
            }
        }
        return ctrue(py);
    }

    // Fallthrough: mismatched shapes after normalisation.
    cfalse(py)
}
