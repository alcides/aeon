//! Random-enumerative synthesizer: generate core Aeon terms randomly,
//! validate (Python `check_type` callback), evaluate (Python fitness
//! callback), and maintain a Pareto front of non-dominated individuals.
//!
//! Term generation is type-directed: given a target `Type`, the
//! generator first unwraps refinements / type polymorphism, then either
//! (a) emits a Literal whose type matches a primitive target, (b) picks
//! a context variable whose return type matches and recurses to fill
//! its arguments, (c) for AbstractionType targets, emits an Abstraction
//! and recurses into the body with the binder added to scope, or (d)
//! emits an If with a random Bool condition. Depth is bounded.

use pyo3::prelude::*;
use pyo3::types::PyList;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};
use std::time::Instant;

use crate::name::Name;
use crate::terms::{Abstraction, Application, If, Literal, Term, TypeApplication, Var};
use crate::substitutions::substitute_vartype;
use crate::typectx::TypingContext;
use crate::types::{
    AbstractionType, RefinedType, RefinementPolymorphism, Type, TypeConstructor, TypePolymorphism,
    TypeVar,
};

// ---- Pareto front --------------------------------------------------------

/// A vector `a` *dominates* `b` (minimization) iff every component of `a`
/// is ≤ the corresponding component of `b` AND at least one is strictly
/// less. Lengths must match.
fn dominates(a: &[f64], b: &[f64]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut strictly_better = false;
    for (x, y) in a.iter().zip(b.iter()) {
        if x > y {
            return false;
        }
        if x < y {
            strictly_better = true;
        }
    }
    strictly_better
}

/// Insert `(score, term)` into a Pareto front (Vec sorted by insertion
/// order). Returns true if it was added (i.e., not dominated by the
/// front; non-dominated entries are also pruned from the front).
fn pareto_insert(front: &mut Vec<(Vec<f64>, PyObject)>, score: Vec<f64>, term: PyObject) -> bool {
    // Check if any existing point dominates the candidate.
    for (s, _) in front.iter() {
        if dominates(s, &score) {
            return false;
        }
        if s == &score {
            // Duplicate score — keep the first one.
            return false;
        }
    }
    // Remove existing points that the candidate dominates.
    front.retain(|(s, _)| !dominates(&score, s));
    front.push((score, term));
    true
}

// ---- Type helpers --------------------------------------------------------

/// Strip refinements / polymorphism wrappers from a type. Returns the
/// "base" inner Type (TypeConstructor, TypeVar, AbstractionType, or
/// fallback to the input if shape is unfamiliar).
fn strip_to_base(py: Python<'_>, ty: PyObject) -> PyObject {
    let mut cur = ty;
    loop {
        let b = cur.bind(py);
        if let Ok(rt) = b.downcast::<RefinedType>() {
            let inner = rt.borrow().type_.clone_ref(py);
            cur = inner;
        } else if let Ok(tp) = b.downcast::<TypePolymorphism>() {
            let body = tp.borrow().body.clone_ref(py);
            cur = body;
        } else if let Ok(rp) = b.downcast::<RefinementPolymorphism>() {
            let body = rp.borrow().body.clone_ref(py);
            cur = body;
        } else {
            return cur;
        }
    }
}

/// Walk a function type chain to its final return-type base.
fn return_base(py: Python<'_>, ty: PyObject) -> PyObject {
    let mut cur = strip_to_base(py, ty);
    loop {
        let b = cur.bind(py);
        if let Ok(at) = b.downcast::<AbstractionType>() {
            let inner = at.borrow().type_.clone_ref(py);
            cur = strip_to_base(py, inner);
        } else {
            return cur;
        }
    }
}

/// True iff the type variable `tv_name` appears in the final return
/// position of `inner` (so we *must* instantiate it to the target type
/// for the application to land on the goal type). If the type variable
/// is referenced only in the arguments, it's free and can be
/// instantiated to anything we have values of.
fn tv_in_return(py: Python<'_>, inner: &PyObject, tv_name: &Py<Name>) -> bool {
    let ret = return_base(py, inner.clone_ref(py));
    let b = ret.bind(py);
    if let Ok(tv) = b.downcast::<TypeVar>() {
        let tv_b = tv.borrow();
        let n = tv_b.name.borrow(py);
        let target = tv_name.borrow(py);
        return n.name == target.name && n.id == target.id;
    }
    false
}

/// Build a concrete TypeConstructor with the given builtin name (Int,
/// Bool, Float, String, Set). No args.
fn mk_concrete(py: Python<'_>, name: &str) -> PyResult<PyObject> {
    let n = Py::new(py, Name { name: name.to_string(), id: 0 })?;
    Ok(Py::new(
        py,
        (
            TypeConstructor { name: n, args: PyList::empty_bound(py).unbind(), loc: crate::loc::default_location(py) },
            Type,
        ),
    )?
    .into_any())
}

/// Pool of concrete types we'll consider when instantiating a free
/// (return-irrelevant) polymorphic type variable. Choosing here is
/// what makes `==`, `!=`, `<`, `<=`, `>`, `>=`, `print`, and `$` usable
/// at every primitive type, not just the goal type.
const CONCRETE_POOL: &[&str] = &["Int", "Bool", "Float", "String", "Set"];

fn random_concrete_type(py: Python<'_>, rng: &mut SmallRng) -> PyResult<PyObject> {
    let n = CONCRETE_POOL[rng.gen_range(0..CONCRETE_POOL.len())];
    mk_concrete(py, n)
}

/// Returns the name of a TypeConstructor (e.g. "Int", "Bool"), or None.
fn tc_name(py: Python<'_>, ty: &PyObject) -> Option<String> {
    let b = ty.bind(py);
    if let Ok(tc) = b.downcast::<TypeConstructor>() {
        return Some(tc.borrow().name.borrow(py).name.clone());
    }
    None
}

/// Collect the parameter types from an AbstractionType chain. Returns
/// `(param_types, _return_type)` — the return type comes back stripped.
fn split_function_type(py: Python<'_>, ty: PyObject) -> (Vec<PyObject>, PyObject) {
    let mut params: Vec<PyObject> = Vec::new();
    let mut cur = strip_to_base(py, ty);
    loop {
        let b = cur.bind(py);
        if let Ok(at) = b.downcast::<AbstractionType>() {
            let at = at.borrow();
            let vt = at.var_type.clone_ref(py);
            let rt = at.type_.clone_ref(py);
            drop(at);
            params.push(vt);
            cur = strip_to_base(py, rt);
        } else {
            return (params, cur);
        }
    }
}

// ---- Term generation -----------------------------------------------------

struct GenCtx<'py> {
    py: Python<'py>,
    rng: &'py mut SmallRng,
    /// list[(Name, Type)] from `TypingContext.vars()`
    ctx_vars: Vec<(Py<Name>, PyObject)>,
    max_depth: u32,
    /// Hard cap on recursive `gen_term` calls within a single trial,
    /// independent of the type-directed `depth` parameter. Polymorphic
    /// targets (TypeVar with no concrete return) bottom out via context
    /// lookups that themselves return more polymorphic functions, so the
    /// typed depth alone is insufficient.
    hard_budget: u32,
}

fn random_int_literal(py: Python<'_>, rng: &mut SmallRng) -> PyResult<PyObject> {
    // Bias toward small/distinguished values.
    let candidates: &[i64] = &[0, 1, -1, 2, 3, 5, 10, -10, 37, 100];
    let v = if rng.gen_bool(0.6) {
        candidates[rng.gen_range(0..candidates.len())]
    } else {
        rng.gen_range(-50..=50)
    };
    let name = Py::new(py, Name { name: "Int".to_string(), id: 0 })?;
    let ty = Py::new(
        py,
        (
            TypeConstructor { name, args: PyList::empty_bound(py).unbind(), loc: crate::loc::default_location(py) },
            Type,
        ),
    )?;
    Ok(Py::new(
        py,
        (
            Literal {
                value: v.into_py(py),
                type_: ty.into_any(),
                loc: crate::loc::default_location(py),
            },
            Term,
        ),
    )?
    .into_any())
}

fn random_bool_literal(py: Python<'_>, rng: &mut SmallRng) -> PyResult<PyObject> {
    let v = rng.gen_bool(0.5);
    let name = Py::new(py, Name { name: "Bool".to_string(), id: 0 })?;
    let ty = Py::new(
        py,
        (
            TypeConstructor { name, args: PyList::empty_bound(py).unbind(), loc: crate::loc::default_location(py) },
            Type,
        ),
    )?;
    Ok(Py::new(
        py,
        (
            Literal {
                value: v.into_py(py),
                type_: ty.into_any(),
                loc: crate::loc::default_location(py),
            },
            Term,
        ),
    )?
    .into_any())
}

fn random_string_literal(py: Python<'_>, rng: &mut SmallRng) -> PyResult<PyObject> {
    // A small bag of distinguished strings: empty, single chars, and a
    // few common words. Random search benefits more from a curated
    // alphabet than from arbitrary garbage.
    let candidates: &[&str] = &["", "a", "b", "c", "x", "y", "hello", "world", "foo", "bar"];
    let v = candidates[rng.gen_range(0..candidates.len())].to_string();
    let name = Py::new(py, Name { name: "String".to_string(), id: 0 })?;
    let ty = Py::new(
        py,
        (
            TypeConstructor { name, args: PyList::empty_bound(py).unbind(), loc: crate::loc::default_location(py) },
            Type,
        ),
    )?;
    Ok(Py::new(
        py,
        (
            Literal {
                value: v.into_py(py),
                type_: ty.into_any(),
                loc: crate::loc::default_location(py),
            },
            Term,
        ),
    )?
    .into_any())
}

fn random_float_literal(py: Python<'_>, rng: &mut SmallRng) -> PyResult<PyObject> {
    let candidates: &[f64] = &[0.0, 1.0, -1.0, 0.5, 2.0, 3.14, -3.14];
    let v = if rng.gen_bool(0.6) {
        candidates[rng.gen_range(0..candidates.len())]
    } else {
        // Sample in [-10, 10].
        rng.gen_range(-10.0..10.0)
    };
    let name = Py::new(py, Name { name: "Float".to_string(), id: 0 })?;
    let ty = Py::new(
        py,
        (
            TypeConstructor { name, args: PyList::empty_bound(py).unbind(), loc: crate::loc::default_location(py) },
            Type,
        ),
    )?;
    Ok(Py::new(
        py,
        (
            Literal {
                value: v.into_py(py),
                type_: ty.into_any(),
                loc: crate::loc::default_location(py),
            },
            Term,
        ),
    )?
    .into_any())
}

/// Returns true if a variable typed `vty` could conceivably produce a
/// value of `target` type. A monomorphic match looks at the
/// return-type-base name; a polymorphic match (vty starts with one or
/// more `TypePolymorphism` foralls) is admitted *iff* the return base is
/// a TypeVar — i.e., we can instantiate the forall to land on `target`.
fn var_returns_type(g: &GenCtx<'_>, vty: &PyObject, target_name: Option<&str>) -> bool {
    let ret = return_base(g.py, vty.clone_ref(g.py));
    let ret_name = tc_name(g.py, &ret);
    if ret_name.as_deref() == target_name {
        return true;
    }
    // Polymorphic vars: return base is a TypeVar; ok if the var has a
    // TypePolymorphism wrapper (so we can emit a TypeApplication).
    if ret_name.is_none() && target_name.is_some() {
        let b = vty.bind(g.py);
        if b.downcast::<TypePolymorphism>().is_ok() {
            return true;
        }
    }
    false
}

fn random_var_of_type(g: &mut GenCtx<'_>, target: &PyObject) -> Option<(Py<Name>, PyObject)> {
    let target_name = tc_name(g.py, &strip_to_base(g.py, target.clone_ref(g.py)));
    let matches: Vec<&(Py<Name>, PyObject)> = g
        .ctx_vars
        .iter()
        .filter(|(_, vty)| var_returns_type(g, vty, target_name.as_deref()))
        .collect();
    if matches.is_empty() {
        return None;
    }
    let pick = matches[g.rng.gen_range(0..matches.len())];
    Some((pick.0.clone_ref(g.py), pick.1.clone_ref(g.py)))
}

fn mk_var(g: &GenCtx<'_>, name: Py<Name>) -> PyResult<PyObject> {
    Ok(Py::new(
        g.py,
        (Var { name, loc: crate::loc::default_location(g.py) }, Term),
    )?
    .into_any())
}

fn mk_application(g: &GenCtx<'_>, fun: PyObject, arg: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(
        g.py,
        (
            Application { fun, arg, loc: crate::loc::default_location(g.py) },
            Term,
        ),
    )?
    .into_any())
}

fn mk_abstraction(g: &GenCtx<'_>, var_name: Py<Name>, body: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(
        g.py,
        (
            Abstraction { var_name, body, loc: crate::loc::default_location(g.py) },
            Term,
        ),
    )?
    .into_any())
}

fn mk_if(g: &GenCtx<'_>, cond: PyObject, then: PyObject, otherwise: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(
        g.py,
        (
            If { cond, then, otherwise, loc: crate::loc::default_location(g.py) },
            Term,
        ),
    )?
    .into_any())
}

fn mk_bool_type(py: Python<'_>) -> PyResult<PyObject> {
    let name = Py::new(py, Name { name: "Bool".to_string(), id: 0 })?;
    Ok(Py::new(
        py,
        (
            TypeConstructor { name, args: PyList::empty_bound(py).unbind(), loc: crate::loc::default_location(py) },
            Type,
        ),
    )?
    .into_any())
}

/// Generate a random core Term targeting `ty`.
fn gen_term(g: &mut GenCtx<'_>, ty: PyObject, depth: u32) -> PyResult<PyObject> {
    let py = g.py;
    // Hard budget guard — emit a fallback literal once we've burned
    // through the allotted recursive calls (prevents stack overflow on
    // pathological cycles through polymorphic context entries).
    if g.hard_budget == 0 {
        return random_int_literal(py, g.rng);
    }
    g.hard_budget -= 1;
    let stripped = strip_to_base(py, ty.clone_ref(py));
    let stripped_b = stripped.bind(py);

    // Abstraction type: emit lambda.
    if let Ok(at) = stripped_b.downcast::<AbstractionType>() {
        let at = at.borrow();
        let var_name = at.var_name.clone_ref(py);
        let var_type = at.var_type.clone_ref(py);
        let ret_type = at.type_.clone_ref(py);
        drop(at);
        // Add the binder to ctx_vars so the body can refer to it.
        g.ctx_vars.push((var_name.clone_ref(py), var_type));
        let body = gen_term(g, ret_type, depth)?;
        g.ctx_vars.pop();
        return mk_abstraction(g, var_name, body);
    }

    // Primitive base type — sometimes emit a literal, sometimes a var.
    let tname = tc_name(py, &stripped);
    let prefer_literal = depth == 0 || g.rng.gen_bool(0.35);
    if prefer_literal {
        if let Some(n) = tname.as_deref() {
            match n {
                "Int" => return random_int_literal(py, g.rng),
                "Bool" => return random_bool_literal(py, g.rng),
                "Float" => return random_float_literal(py, g.rng),
                "String" => return random_string_literal(py, g.rng),
                _ => {}
            }
        }
    }

    // If depth allows, try an If-expression occasionally.
    if depth > 0 && g.rng.gen_bool(0.15) {
        let bool_ty = mk_bool_type(py)?;
        let cond = gen_term(g, bool_ty, depth - 1)?;
        let then = gen_term(g, ty.clone_ref(py), depth - 1)?;
        let otherwise = gen_term(g, ty.clone_ref(py), depth - 1)?;
        return mk_if(g, cond, then, otherwise);
    }

    // Try a context variable whose return type matches; if it's a
    // function, build an application chain by filling its args.
    if let Some((vname, vty)) = random_var_of_type(g, &ty) {
        // Peel outer `forall` quantifiers. For each bound type variable
        // we decide between two instantiations:
        //   * If the variable appears in the return position of the
        //     inner type, we *must* set it to the target — that's how
        //     the application's result lands on the goal type. (Used
        //     for the arithmetic operators `+ - * /` whose
        //     `forall a. a -> a -> a` signature ties argument and
        //     return types together.)
        //   * Otherwise the variable is argument-only and can be any
        //     concrete primitive (`Int`, `Bool`, `Float`, `String`,
        //     `Set`). This is what lets `==`, `!=`, `<` and friends
        //     (`forall a. a -> a -> Bool`) generate comparisons at any
        //     primitive type, not just the goal type.
        let inst_target = strip_to_base(py, ty.clone_ref(py));
        let mut inst_ty = vty.clone_ref(py);
        let mut term = mk_var(g, vname)?;
        loop {
            let b = inst_ty.bind(py);
            if let Ok(tp) = b.downcast::<TypePolymorphism>() {
                let tp = tp.borrow();
                let tv_name = tp.name.clone_ref(py);
                let body = tp.body.clone_ref(py);
                drop(tp);
                let inst = if tv_in_return(py, &body, &tv_name) {
                    inst_target.clone_ref(py)
                } else {
                    random_concrete_type(py, g.rng)?
                };
                term = Py::new(
                    py,
                    (
                        TypeApplication {
                            body: term,
                            type_: inst.clone_ref(py),
                            loc: crate::loc::default_location(py),
                        },
                        Term,
                    ),
                )?
                .into_any();
                inst_ty = substitute_vartype(py, body, inst, tv_name)?;
            } else {
                break;
            }
        }
        let (params, _ret) = split_function_type(py, inst_ty);
        let next_depth = depth.saturating_sub(1);
        for ptype in params {
            let arg = gen_term(g, ptype, next_depth)?;
            term = mk_application(g, term, arg)?;
        }
        return Ok(term);
    }

    // Fallback: literal best guess.
    if let Some(n) = tname.as_deref() {
        match n {
            "Int" => return random_int_literal(py, g.rng),
            "Bool" => return random_bool_literal(py, g.rng),
            "Float" => return random_float_literal(py, g.rng),
            _ => {}
        }
    }

    // Final fallback: pick any variable from the context.
    if !g.ctx_vars.is_empty() {
        let pick = &g.ctx_vars[g.rng.gen_range(0..g.ctx_vars.len())];
        return mk_var(g, pick.0.clone_ref(py));
    }

    // Truly empty context: just an Int 0.
    random_int_literal(py, g.rng)
}

// ---- The synthesizer pyclass --------------------------------------------

#[pyclass(module = "aeon_rs")]
pub struct RustEnumSynthesizer {
    seed: u64,
    max_depth: u32,
}

#[pymethods]
impl RustEnumSynthesizer {
    #[new]
    #[pyo3(signature = (seed = 42, max_depth = 5))]
    fn py_new(seed: u64, max_depth: u32) -> Self {
        RustEnumSynthesizer { seed, max_depth }
    }

    #[getter]
    fn pareto_front_size(&self) -> u32 {
        // For introspection from tests; the last run's front size is
        // returned via the alternative `synthesize_with_front` entry.
        0
    }

    /// Matches the Python `Synthesizer.synthesize` ABC.
    #[pyo3(signature = (
        ctx, ty, validate, evaluate, fun_name, metadata,
        budget = 60.0, ui = None,
    ))]
    fn synthesize(
        &self,
        py: Python<'_>,
        ctx: PyObject,
        ty: PyObject,
        validate: PyObject,
        evaluate: PyObject,
        fun_name: Py<Name>,
        metadata: PyObject,
        budget: f64,
        ui: Option<PyObject>,
    ) -> PyResult<PyObject> {
        let _ = (fun_name, metadata);

        // Duck-type: any object with a `vars() -> list[(Name, Type)]`
        // method works (Rust TypingContext or master's Python TypingContext).
        let vars_list = ctx.call_method0(py, "vars")?;
        let vars_b = vars_list.bind(py).downcast::<PyList>()?;
        let mut ctx_vars: Vec<(Py<Name>, PyObject)> = Vec::with_capacity(vars_b.len());
        for i in 0..vars_b.len() {
            let item = vars_b.get_item(i)?;
            let n: Py<Name> = item.get_item(0)?.downcast::<Name>()?.clone().unbind();
            let t = item.get_item(1)?.unbind();
            ctx_vars.push((n, t));
        }

        let mut rng = SmallRng::seed_from_u64(self.seed);

        let mut front: Vec<(Vec<f64>, PyObject)> = Vec::new();
        let start = Instant::now();
        let budget_dur = std::time::Duration::from_secs_f64(budget);

        let mut attempts: u64 = 0;
        let mut validated: u64 = 0;
        let mut evaluated: u64 = 0;

        // Stash the original `ctx_vars` length so we can roll back binder
        // additions made during one trial.
        let initial_vars = ctx_vars.len();
        while start.elapsed() < budget_dur {
            attempts += 1;
            // Reset to initial scope for each attempt.
            ctx_vars.truncate(initial_vars);
            let mut g = GenCtx {
                py,
                rng: &mut rng,
                ctx_vars,
                max_depth: self.max_depth,
                // Recursion budget: each gen_term call consumes one.
                // 100 is generous for any sane term tree.
                hard_budget: 100,
            };
            let term_result = gen_term(&mut g, ty.clone_ref(py), self.max_depth);
            let GenCtx { ctx_vars: cv, .. } = g;
            ctx_vars = cv;
            let term = match term_result {
                Ok(t) => t,
                Err(_) => continue,
            };

            // Validate (typecheck) via Python.
            let valid = match validate.call1(py, (term.clone_ref(py),)) {
                Ok(v) => match v.extract::<bool>(py) {
                    Ok(b) => b,
                    Err(_) => false,
                },
                Err(_) => false,
            };
            if !valid {
                continue;
            }
            validated += 1;

            // Evaluate (fitness) via Python — returns list[float].
            let score_obj = match evaluate.call1(py, (term.clone_ref(py),)) {
                Ok(v) => v,
                Err(_) => continue,
            };
            evaluated += 1;
            let score: Vec<f64> = match score_obj.extract::<Vec<f64>>(py) {
                Ok(s) => s,
                Err(_) => continue,
            };

            // Skip clearly broken scores.
            if score.iter().any(|x| !x.is_finite()) {
                continue;
            }

            let is_better = pareto_insert(&mut front, score.clone(), term.clone_ref(py));

            // Notify the UI if present.
            if let Some(ui) = ui.as_ref() {
                let _ = ui.call_method1(
                    py,
                    "register",
                    (
                        term.clone_ref(py),
                        score.clone(),
                        start.elapsed().as_secs_f64(),
                        is_better,
                    ),
                );
            }
        }

        let _ = attempts;
        let _ = validated;
        let _ = evaluated;

        // Return the term with the lexicographically smallest score from
        // the Pareto front (a deterministic, single-objective-friendly
        // tie-breaker). If the front is empty, return None.
        if front.is_empty() {
            return Ok(py.None());
        }
        let mut best_idx = 0usize;
        for i in 1..front.len() {
            // Lexicographic compare.
            let cur = &front[i].0;
            let best = &front[best_idx].0;
            let mut chose = false;
            for (a, b) in cur.iter().zip(best.iter()) {
                if a < b {
                    best_idx = i;
                    chose = true;
                    break;
                } else if a > b {
                    chose = true;
                    break;
                }
            }
            let _ = chose;
        }
        Ok(front.remove(best_idx).1)
    }

    /// Same as `synthesize` but also returns `(term, pareto_front)` where
    /// the front is a `list[(list[float], Term)]`. Useful for tests /
    /// introspection.
    #[pyo3(signature = (
        ctx, ty, validate, evaluate, fun_name, metadata,
        budget = 60.0, ui = None,
    ))]
    fn synthesize_with_front(
        &self,
        py: Python<'_>,
        ctx: Py<TypingContext>,
        ty: PyObject,
        validate: PyObject,
        evaluate: PyObject,
        fun_name: Py<Name>,
        metadata: PyObject,
        budget: f64,
        ui: Option<PyObject>,
    ) -> PyResult<(PyObject, PyObject)> {
        let _ = (fun_name, metadata);

        let ctx_b = ctx.borrow(py);
        let vars_list = ctx_b.vars(py)?;
        drop(ctx_b);
        let vars_b = vars_list.bind(py);
        let mut ctx_vars: Vec<(Py<Name>, PyObject)> = Vec::with_capacity(vars_b.len());
        for i in 0..vars_b.len() {
            let item = vars_b.get_item(i)?;
            let n: Py<Name> = item.get_item(0)?.downcast::<Name>()?.clone().unbind();
            let t = item.get_item(1)?.unbind();
            ctx_vars.push((n, t));
        }

        let mut rng = SmallRng::seed_from_u64(self.seed);
        let mut front: Vec<(Vec<f64>, PyObject)> = Vec::new();
        let start = Instant::now();
        let budget_dur = std::time::Duration::from_secs_f64(budget);
        let initial_vars = ctx_vars.len();

        while start.elapsed() < budget_dur {
            ctx_vars.truncate(initial_vars);
            let mut g = GenCtx {
                py,
                rng: &mut rng,
                ctx_vars,
                max_depth: self.max_depth,
                // Recursion budget: each gen_term call consumes one.
                // 100 is generous for any sane term tree.
                hard_budget: 100,
            };
            let term_result = gen_term(&mut g, ty.clone_ref(py), self.max_depth);
            let GenCtx { ctx_vars: cv, .. } = g;
            ctx_vars = cv;
            let term = match term_result {
                Ok(t) => t,
                Err(_) => continue,
            };
            let valid = match validate.call1(py, (term.clone_ref(py),)) {
                Ok(v) => v.extract::<bool>(py).unwrap_or(false),
                Err(_) => false,
            };
            if !valid {
                continue;
            }
            let score_obj = match evaluate.call1(py, (term.clone_ref(py),)) {
                Ok(v) => v,
                Err(_) => continue,
            };
            let score: Vec<f64> = match score_obj.extract::<Vec<f64>>(py) {
                Ok(s) => s,
                Err(_) => continue,
            };
            if score.iter().any(|x| !x.is_finite()) {
                continue;
            }
            let is_better = pareto_insert(&mut front, score.clone(), term.clone_ref(py));
            if let Some(ui) = ui.as_ref() {
                let _ = ui.call_method1(
                    py,
                    "register",
                    (term.clone_ref(py), score, start.elapsed().as_secs_f64(), is_better),
                );
            }
        }

        let front_list = PyList::empty_bound(py);
        for (s, t) in front.iter() {
            let s_list = PyList::empty_bound(py);
            for v in s {
                s_list.append(*v)?;
            }
            let tup = pyo3::types::PyTuple::new_bound(py, &[s_list.into_any().unbind(), t.clone_ref(py)]);
            front_list.append(tup)?;
        }

        // Pick best by lexicographic score.
        let best: PyObject = if front.is_empty() {
            py.None()
        } else {
            let mut best_idx = 0usize;
            for i in 1..front.len() {
                let cur = &front[i].0;
                let bestv = &front[best_idx].0;
                let mut decided = false;
                for (a, b) in cur.iter().zip(bestv.iter()) {
                    if a < b {
                        best_idx = i;
                        decided = true;
                        break;
                    } else if a > b {
                        decided = true;
                        break;
                    }
                }
                let _ = decided;
            }
            front[best_idx].1.clone_ref(py)
        };

        Ok((best, front_list.unbind().into_any()))
    }
}

// Silence unused warnings.
#[allow(dead_code)]
fn _force(t: TypeVar) {
    let _ = t;
}
