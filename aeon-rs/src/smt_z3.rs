//! Native Rust z3 layer: `smt_valid`, `translate`, and the variable /
//! function / sort builders. Replaces the Python z3-py implementation in
//! `aeon.verification.smt`.
//!
//! Lifetime story: z3 ASTs all hold a `&'ctx Context` reference. We sidestep
//! the lifetime problem by leaking a single process-wide `Context` and
//! handing out `&'static Context` everywhere. The Python GIL serialises all
//! calls into this module, so a single global `Solver` (behind a `Mutex` to
//! satisfy `OnceLock<_>: Sync`) is fine.

use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList};
use z3::ast::{Ast, Bool, Dynamic, Int, Real, Set, String as Z3String};
use z3::{Config, Context, FuncDecl, SatResult, Solver, Sort};

use crate::liquid::{
    LiquidApp, LiquidLiteralBool, LiquidLiteralFloat, LiquidLiteralInt, LiquidLiteralString,
    LiquidTerm, LiquidVar,
};
use crate::name::Name;
use crate::smt_ctx::CanonicConstraint;
use crate::smt_flatten::flatten;
use crate::types::{AbstractionType, Top, TypeConstructor, TypeVar};
use crate::vcs::alpha_key;

// =============================================================================
// Global z3 Context + Solver
// =============================================================================

/// Newtype wrapper to assert that a z3 type is safe to share across threads.
/// Every Rust call into this module is made while the Python GIL is held,
/// so the *effective* concurrency model is single-threaded; the unsafe impls
/// are sound under that invariant.
struct GilSafe<T>(T);
unsafe impl<T> Send for GilSafe<T> {}
unsafe impl<T> Sync for GilSafe<T> {}

static Z3_CTX: OnceLock<GilSafe<*const Context>> = OnceLock::new();

/// The process-wide z3 [`Context`]. Lazily initialised; never freed — the
/// pointer lives for the lifetime of the extension module.
fn ctx() -> &'static Context {
    let p = Z3_CTX.get_or_init(|| {
        let cfg = Config::new();
        let leaked: &'static Context = Box::leak(Box::new(Context::new(&cfg)));
        GilSafe(leaked as *const Context)
    });
    unsafe { &*(p.0) }
}

static SOLVER: OnceLock<Mutex<GilSafe<Solver<'static>>>> = OnceLock::new();

fn solver() -> &'static Mutex<GilSafe<Solver<'static>>> {
    SOLVER.get_or_init(|| {
        let s = Solver::new(ctx());
        // Match the Python `s.set(timeout=200)` budget.
        let mut params = z3::Params::new(ctx());
        params.set_u32("timeout", 200);
        s.set_params(&params);
        Mutex::new(GilSafe(s))
    })
}

// =============================================================================
// alpha_key-keyed result cache
// =============================================================================

static SMT_VALID_CACHE: OnceLock<Mutex<HashMap<String, bool>>> = OnceLock::new();

fn cache() -> &'static Mutex<HashMap<String, bool>> {
    SMT_VALID_CACHE.get_or_init(|| Mutex::new(HashMap::new()))
}

// =============================================================================
// Sort & variable helpers
// =============================================================================

/// Sort cache for user-defined sorts (uninterpreted `DeclareSort`).
static USER_SORTS: OnceLock<Mutex<GilSafe<HashMap<String, Sort<'static>>>>> = OnceLock::new();
fn user_sorts() -> &'static Mutex<GilSafe<HashMap<String, Sort<'static>>>> {
    USER_SORTS.get_or_init(|| Mutex::new(GilSafe(HashMap::new())))
}

/// Get the z3 [`Sort`] for an Aeon base [`Type`]. Mirrors `get_sort`.
fn get_sort(py: Python<'_>, base: &PyObject) -> PyResult<Sort<'static>> {
    let bound = base.bind(py);
    if bound.is_instance_of::<Top>() {
        return Ok(Sort::int(ctx()));
    }
    if let Ok(tc) = bound.downcast::<TypeConstructor>() {
        let tc = tc.borrow();
        let name = tc.name.borrow(py).name.clone();
        return Ok(sort_from_name(&name));
    }
    if bound.is_instance_of::<TypeVar>() {
        return Err(pyo3::exceptions::PyAssertionError::new_err(
            "TypeVar should not be used in SMT solver.",
        ));
    }
    Err(pyo3::exceptions::PyException::new_err(format!(
        "SMT sort of {} not implemented.",
        bound.repr()?.to_string()
    )))
}

/// Map a base-type name to its z3 sort, declaring an uninterpreted sort
/// the first time we see a capitalised name we don't already know.
fn sort_from_name(name: &str) -> Sort<'static> {
    match name {
        "Top" | "Int" => Sort::int(ctx()),
        "Bool" => Sort::bool(ctx()),
        "Float" => Sort::real(ctx()),
        "String" => Sort::string(ctx()),
        "Set" => Sort::set(ctx(), &Sort::int(ctx())),
        _ => {
            // Uppercase identifiers become uninterpreted sorts; lowercase
            // collapse to Int (matches Python `get_sort`).
            if !name.chars().next().map(|c| c.is_uppercase()).unwrap_or(false) {
                return Sort::int(ctx());
            }
            let mut guard = user_sorts().lock().unwrap();
            let cache = &mut guard.0;
            if let Some(s) = cache.get(name) {
                return s.clone();
            }
            let s = Sort::uninterpreted(ctx(), name.into());
            cache.insert(name.to_string(), s.clone());
            s
        }
    }
}

/// Build a z3 constant of the right sort for `base`. Mirrors `make_variable`
/// (variables, not functions — functions go through `uncurry` + `FuncDecl`).
fn make_variable_const(py: Python<'_>, name: &str, base: &PyObject) -> PyResult<Dynamic<'static>> {
    let bound = base.bind(py);
    if bound.is_instance_of::<Top>() {
        return Ok(Dynamic::from_ast(&Int::new_const(ctx(), name)));
    }
    if let Ok(tc) = bound.downcast::<TypeConstructor>() {
        let tc = tc.borrow();
        let tname = tc.name.borrow(py).name.clone();
        return Ok(match tname.as_str() {
            "Top" | "Int" => Dynamic::from_ast(&Int::new_const(ctx(), name)),
            "Bool" => Dynamic::from_ast(&Bool::new_const(ctx(), name)),
            "Float" => Dynamic::from_ast(&Real::new_const(ctx(), name)),
            "String" => Dynamic::from_ast(&Z3String::new_const(ctx(), name)),
            "Set" => Dynamic::from_ast(&Set::new_const(ctx(), name, &Sort::int(ctx()))),
            _ => {
                let s = sort_from_name(&tname);
                // No direct Dynamic constructor for arbitrary sorts; use a
                // 0-arity FuncDecl as the const builder (this is exactly
                // what z3 does internally for constants).
                let fd = FuncDecl::new(ctx(), name, &[], &s);
                fd.apply(&[])
            }
        });
    }
    if bound.is_instance_of::<TypeVar>() {
        return Ok(Dynamic::from_ast(&Int::new_const(ctx(), name)));
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "make_variable: unexpected base type {}",
        bound.repr()?.to_string()
    )))
}

// =============================================================================
// uncurry — flatten AbstractionType to ([input sorts], output sort)
// =============================================================================
//
// Mirrors the Rust port already in smt_helpers::uncurry, but here we return
// z3 sorts directly so the result can feed into `FuncDecl::new`.

fn uncurry_to_sorts(
    py: Python<'_>,
    ty: &PyObject,
) -> PyResult<(Vec<Sort<'static>>, Sort<'static>)> {
    let bound = ty.bind(py);
    if let Ok(_at) = bound.downcast::<AbstractionType>() {
        // Re-use the existing Rust uncurry helper for the type-level walk.
        let tuple = crate::smt_helpers::uncurry(py, ty.clone_ref(py))?;
        let inputs_obj = tuple.get_item(0)?;
        let output_obj = tuple.get_item(1)?;
        let inputs = inputs_obj.downcast::<PyList>()?;
        let mut in_sorts: Vec<Sort<'static>> = Vec::with_capacity(inputs.len());
        for i in 0..inputs.len() {
            let item = inputs.get_item(i)?.unbind();
            in_sorts.push(get_sort(py, &item)?);
        }
        let out_obj: PyObject = output_obj.unbind();
        let out_sort = get_sort(py, &out_obj)?;
        return Ok((in_sorts, out_sort));
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(
        "uncurry_to_sorts: type is not an AbstractionType",
    ))
}

// =============================================================================
// Function-declaration & environment caches
// =============================================================================

enum EnvEntry {
    Var(Dynamic<'static>),
    Func(FuncDecl<'static>),
    /// One of the built-in arithmetic / boolean operators (`+`, `&&`, etc.).
    /// Handled inline by `translate_liq_app`.
    BuiltinOp,
}

fn builtin_ops() -> &'static std::collections::HashSet<&'static str> {
    static OPS: OnceLock<std::collections::HashSet<&'static str>> = OnceLock::new();
    OPS.get_or_init(|| {
        let mut s = std::collections::HashSet::new();
        for op in &[
            "==", "!=", "<", "<=", ">", ">=", "!", "&&", "||", "+", "-", "*", "/", "%", "-->",
            "Set_empty", "Set_sng", "Set_cup", "Set_cap", "Set_dif", "Set_mem", "Set_sub",
        ] {
            s.insert(*op);
        }
        s
    })
}

/// Build the per-leaf environment: variables (z3 constants) and function
/// declarations (uninterpreted z3 functions). Mirrors `mk_vars` + `mk_funs`
/// from the Python implementation.
fn build_env(
    py: Python<'_>,
    variables: &Bound<'_, PyDict>,
    functions: &Bound<'_, PyDict>,
) -> PyResult<HashMap<String, EnvEntry>> {
    let mut env: HashMap<String, EnvEntry> = HashMap::new();

    for (k, v) in variables.iter() {
        let name: String = k.extract()?;
        let v_obj: PyObject = v.unbind();
        let c = make_variable_const(py, &name, &v_obj)?;
        env.insert(name, EnvEntry::Var(c));
    }

    for (k, v) in functions.iter() {
        let name: String = k.extract()?;
        let v_obj: PyObject = v.unbind();
        // Built-in operator? (e.g. `==`, `+`). Handled inline at app time.
        if builtin_ops().contains(name.as_str()) {
            env.insert(name, EnvEntry::BuiltinOp);
            continue;
        }
        // Otherwise it's an uninterpreted (or reflected) function.
        let (input_sorts, output_sort) = uncurry_to_sorts(py, &v_obj)?;
        let input_refs: Vec<&Sort<'static>> = input_sorts.iter().collect();
        let fd = FuncDecl::new(ctx(), name.as_str(), &input_refs, &output_sort);
        env.insert(name, EnvEntry::Func(fd));
    }

    Ok(env)
}

// =============================================================================
// translate_liq — LiquidTerm -> z3 Dynamic
// =============================================================================

fn translate_liq(
    py: Python<'_>,
    t: &PyObject,
    env: &HashMap<String, EnvEntry>,
) -> PyResult<Dynamic<'static>> {
    let bound = t.bind(py);

    if let Ok(b) = bound.downcast::<LiquidLiteralBool>() {
        let b = b.borrow();
        return Ok(Dynamic::from_ast(&Bool::from_bool(ctx(), b.value)));
    }
    if let Ok(i) = bound.downcast::<LiquidLiteralInt>() {
        let i = i.borrow();
        return Ok(Dynamic::from_ast(&Int::from_i64(ctx(), i.value)));
    }
    if let Ok(f) = bound.downcast::<LiquidLiteralFloat>() {
        let f = f.borrow();
        // Z3 has no double literal; encode as Real from a string.
        let s = format!("{}", f.value);
        let r = Real::from_real_str(ctx(), &s, "1")
            .ok_or_else(|| pyo3::exceptions::PyValueError::new_err("bad real literal"))?;
        return Ok(Dynamic::from_ast(&r));
    }
    if let Ok(s) = bound.downcast::<LiquidLiteralString>() {
        let s = s.borrow();
        let z3s = Z3String::from_str(ctx(), &s.value).map_err(|_| {
            pyo3::exceptions::PyValueError::new_err("string contains NUL — cannot encode")
        })?;
        return Ok(Dynamic::from_ast(&z3s));
    }
    if let Ok(v) = bound.downcast::<LiquidVar>() {
        let v = v.borrow();
        let name = v.name.borrow(py).__str__();
        return resolve_var(env, &name);
    }
    if let Ok(app) = bound.downcast::<LiquidApp>() {
        return translate_liq_app(py, &app.borrow(), env);
    }

    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Cannot translate {}",
        bound.repr()?.to_string()
    )))
}

fn resolve_var(env: &HashMap<String, EnvEntry>, name: &str) -> PyResult<Dynamic<'static>> {
    match env.get(name) {
        Some(EnvEntry::Var(c)) => Ok(c.clone()),
        Some(EnvEntry::Func(_)) => Err(pyo3::exceptions::PyKeyError::new_err(format!(
            "variable {} is bound to a function, not a value",
            name
        ))),
        Some(EnvEntry::BuiltinOp) => Err(pyo3::exceptions::PyKeyError::new_err(format!(
            "operator {} cannot appear bare (as LiquidVar)",
            name
        ))),
        None => {
            // Built-in constants like Set_empty.
            if name == "Set_empty" {
                return Ok(Dynamic::from_ast(&Set::empty(ctx(), &Sort::int(ctx()))));
            }
            Err(pyo3::exceptions::PyKeyError::new_err(format!(
                "Variable {} not found in SMT context",
                name
            )))
        }
    }
}

fn translate_liq_app(
    py: Python<'_>,
    app: &LiquidApp,
    env: &HashMap<String, EnvEntry>,
) -> PyResult<Dynamic<'static>> {
    // Built-in operators are keyed by the plain ASCII name. Declared
    // functions (uninterpreted / reflected) are keyed by `str(name)`,
    // which carries the superscripted ID — `with_function` stored them
    // that way.
    let raw_name = app.fun.borrow(py).name.clone();
    let full_name = app.fun.borrow(py).__str__();
    let args_list = app.args.bind(py);
    let mut args: Vec<Dynamic<'static>> = Vec::with_capacity(args_list.len());
    for i in 0..args_list.len() {
        let a = args_list.get_item(i)?.unbind();
        args.push(translate_liq(py, &a, env)?);
    }

    if let Some(result) = apply_builtin(&raw_name, &args)? {
        return Ok(result);
    }

    match env.get(&full_name) {
        Some(EnvEntry::Func(fd)) => {
            let arg_refs: Vec<&dyn Ast> = args.iter().map(|d| d as &dyn Ast).collect();
            Ok(fd.apply(&arg_refs))
        }
        Some(EnvEntry::Var(_)) => Err(pyo3::exceptions::PyKeyError::new_err(format!(
            "{} is a value, not a function",
            full_name
        ))),
        Some(EnvEntry::BuiltinOp) | None => Err(pyo3::exceptions::PyKeyError::new_err(format!(
            "Function {} not found.",
            full_name
        ))),
    }
}

/// Apply a built-in arithmetic / boolean / set operator. Returns `Ok(None)`
/// if `fname` isn't a built-in (so the caller can fall through to function
/// declarations).
fn apply_builtin(fname: &str, args: &[Dynamic<'static>]) -> PyResult<Option<Dynamic<'static>>> {
    let result: Option<Dynamic<'static>> = match fname {
        "==" => Some(Dynamic::from_ast(&args[0]._eq(&args[1]))),
        "!=" => Some(Dynamic::from_ast(&args[0]._eq(&args[1]).not())),
        "!" => {
            let b = args[0]
                .as_bool()
                .ok_or_else(|| pyo3::exceptions::PyValueError::new_err("! expects Bool"))?;
            Some(Dynamic::from_ast(&b.not()))
        }
        "&&" => {
            let a = args[0].as_bool().ok_or_else(arg_bool_err)?;
            let b = args[1].as_bool().ok_or_else(arg_bool_err)?;
            Some(Dynamic::from_ast(&Bool::and(ctx(), &[&a, &b])))
        }
        "||" => {
            let a = args[0].as_bool().ok_or_else(arg_bool_err)?;
            let b = args[1].as_bool().ok_or_else(arg_bool_err)?;
            Some(Dynamic::from_ast(&Bool::or(ctx(), &[&a, &b])))
        }
        "-->" => {
            let a = args[0].as_bool().ok_or_else(arg_bool_err)?;
            let b = args[1].as_bool().ok_or_else(arg_bool_err)?;
            Some(Dynamic::from_ast(&a.implies(&b)))
        }
        "<" | "<=" | ">" | ">=" | "+" | "-" | "*" | "/" => Some(arith(fname, args)?),
        "%" => {
            let a = args[0]
                .as_int()
                .ok_or_else(|| pyo3::exceptions::PyValueError::new_err("% expects Int"))?;
            let b = args[1]
                .as_int()
                .ok_or_else(|| pyo3::exceptions::PyValueError::new_err("% expects Int"))?;
            Some(Dynamic::from_ast(&a.modulo(&b)))
        }
        "Set_sng" => {
            let e = args[0]
                .as_int()
                .ok_or_else(|| pyo3::exceptions::PyValueError::new_err("Set_sng expects Int"))?;
            let empty = Set::empty(ctx(), &Sort::int(ctx()));
            Some(Dynamic::from_ast(&empty.add(&e)))
        }
        "Set_cup" => {
            let a = args[0].as_set().ok_or_else(arg_set_err)?;
            let b = args[1].as_set().ok_or_else(arg_set_err)?;
            Some(Dynamic::from_ast(&Set::set_union(ctx(), &[&a, &b])))
        }
        "Set_cap" => {
            let a = args[0].as_set().ok_or_else(arg_set_err)?;
            let b = args[1].as_set().ok_or_else(arg_set_err)?;
            Some(Dynamic::from_ast(&Set::intersect(ctx(), &[&a, &b])))
        }
        "Set_dif" => {
            let a = args[0].as_set().ok_or_else(arg_set_err)?;
            let b = args[1].as_set().ok_or_else(arg_set_err)?;
            Some(Dynamic::from_ast(&a.difference(&b)))
        }
        "Set_mem" => {
            let e = args[0].as_int().ok_or_else(arg_int_err)?;
            let s = args[1].as_set().ok_or_else(arg_set_err)?;
            Some(Dynamic::from_ast(&s.member(&e)))
        }
        "Set_sub" => {
            let a = args[0].as_set().ok_or_else(arg_set_err)?;
            let b = args[1].as_set().ok_or_else(arg_set_err)?;
            Some(Dynamic::from_ast(&a.set_subset(&b)))
        }
        _ => None,
    };
    Ok(result)
}

fn arith(op: &str, args: &[Dynamic<'static>]) -> PyResult<Dynamic<'static>> {
    // Both args are either both Int or both Real (Python relies on z3-py's
    // implicit lifting; we make the dispatch explicit).
    if let (Some(a), Some(b)) = (args[0].as_int(), args[1].as_int()) {
        return Ok(match op {
            "<" => Dynamic::from_ast(&a.lt(&b)),
            "<=" => Dynamic::from_ast(&a.le(&b)),
            ">" => Dynamic::from_ast(&a.gt(&b)),
            ">=" => Dynamic::from_ast(&a.ge(&b)),
            "+" => Dynamic::from_ast(&Int::add(ctx(), &[&a, &b])),
            "-" => Dynamic::from_ast(&Int::sub(ctx(), &[&a, &b])),
            "*" => Dynamic::from_ast(&Int::mul(ctx(), &[&a, &b])),
            "/" => Dynamic::from_ast(&a.div(&b)),
            _ => unreachable!(),
        });
    }
    if let (Some(a), Some(b)) = (args[0].as_real(), args[1].as_real()) {
        return Ok(match op {
            "<" => Dynamic::from_ast(&a.lt(&b)),
            "<=" => Dynamic::from_ast(&a.le(&b)),
            ">" => Dynamic::from_ast(&a.gt(&b)),
            ">=" => Dynamic::from_ast(&a.ge(&b)),
            "+" => Dynamic::from_ast(&Real::add(ctx(), &[&a, &b])),
            "-" => Dynamic::from_ast(&Real::sub(ctx(), &[&a, &b])),
            "*" => Dynamic::from_ast(&Real::mul(ctx(), &[&a, &b])),
            "/" => Dynamic::from_ast(&a.div(&b)),
            _ => unreachable!(),
        });
    }
    // Mixed Int/Real — promote the Int side.
    let (a, b) = match (args[0].as_int(), args[1].as_real()) {
        (Some(ai), Some(br)) => (Real::from_int(&ai), br),
        _ => match (args[0].as_real(), args[1].as_int()) {
            (Some(ar), Some(bi)) => (ar, Real::from_int(&bi)),
            _ => {
                return Err(pyo3::exceptions::PyValueError::new_err(format!(
                    "arith({}): unexpected operand sorts",
                    op
                )));
            }
        },
    };
    Ok(match op {
        "<" => Dynamic::from_ast(&a.lt(&b)),
        "<=" => Dynamic::from_ast(&a.le(&b)),
        ">" => Dynamic::from_ast(&a.gt(&b)),
        ">=" => Dynamic::from_ast(&a.ge(&b)),
        "+" => Dynamic::from_ast(&Real::add(ctx(), &[&a, &b])),
        "-" => Dynamic::from_ast(&Real::sub(ctx(), &[&a, &b])),
        "*" => Dynamic::from_ast(&Real::mul(ctx(), &[&a, &b])),
        "/" => Dynamic::from_ast(&a.div(&b)),
        _ => unreachable!(),
    })
}

fn arg_bool_err() -> PyErr {
    pyo3::exceptions::PyValueError::new_err("expected Bool argument")
}
fn arg_int_err() -> PyErr {
    pyo3::exceptions::PyValueError::new_err("expected Int argument")
}
fn arg_set_err() -> PyErr {
    pyo3::exceptions::PyValueError::new_err("expected Set argument")
}

// =============================================================================
// translate — CanonicConstraint -> Bool z3 expression
// =============================================================================

/// Returns `Ok(None)` to signal "skip this leaf" (the Python encoder uses
/// `False`/exception for skipped leaves; we use Option for clarity).
fn translate(
    py: Python<'_>,
    cc: &CanonicConstraint,
) -> PyResult<Option<Bool<'static>>> {
    let env = build_env(py, cc.variables.bind(py), cc.functions.bind(py))?;

    let premise = match translate_liq_safe(py, &cc.premise, &env)? {
        Some(d) => d,
        None => return Ok(None),
    };
    let conclusion = match translate_liq_safe(py, &cc.conclusion, &env)? {
        Some(d) => d,
        None => return Ok(None),
    };

    // If the conclusion is the literal True, we can short-circuit to "valid".
    if let Some(b) = conclusion.as_bool() {
        if b.as_bool() == Some(true) {
            return Ok(None);
        }
    }

    let premise_b = premise
        .as_bool()
        .ok_or_else(|| pyo3::exceptions::PyValueError::new_err("premise must be Bool"))?;
    let concl_b = conclusion
        .as_bool()
        .ok_or_else(|| pyo3::exceptions::PyValueError::new_err("conclusion must be Bool"))?;

    let distinct = constructor_distinctness(py, &env)?;
    let full_premise = if distinct.is_empty() {
        premise_b
    } else {
        let mut all: Vec<&Bool<'static>> = Vec::with_capacity(distinct.len() + 1);
        all.push(&premise_b);
        for d in &distinct {
            all.push(d);
        }
        Bool::and(ctx(), &all)
    };

    Ok(Some(Bool::and(ctx(), &[&full_premise, &concl_b.not()])))
}

/// Like `translate_liq` but maps ZeroDivision-like panics into `None` so
/// the caller can skip the leaf (matches Python's `except ZeroDivisionError`).
fn translate_liq_safe(
    py: Python<'_>,
    t: &PyObject,
    env: &HashMap<String, EnvEntry>,
) -> PyResult<Option<Dynamic<'static>>> {
    // The Python version catches `ZeroDivisionError` from division literal
    // simplification; with z3 division is symbolic so we don't actually need
    // the guard. Keep the signature in case future translators need it.
    translate_liq(py, t, env).map(Some)
}

// =============================================================================
// Constructor distinctness — mirror `_constructor_distinctness`
// =============================================================================

fn constructor_distinctness(
    _py: Python<'_>,
    env: &HashMap<String, EnvEntry>,
) -> PyResult<Vec<Bool<'static>>> {
    // Build base-name -> Dynamic. Variable keys may carry trailing Unicode
    // superscripts (alpha-renaming markers) — strip those to recover the
    // original constructor name.
    let mut base_to_dyn: HashMap<String, Dynamic<'static>> = HashMap::new();
    for (k, v) in env.iter() {
        if let EnvEntry::Var(d) = v {
            let stripped = k.trim_end_matches(|c: char| {
                matches!(
                    c,
                    '⁰' | '¹' | '²' | '³' | '⁴' | '⁵' | '⁶' | '⁷' | '⁸' | '⁹'
                )
            });
            base_to_dyn.insert(stripped.to_string(), d.clone());
        }
    }

    let mut out: Vec<Bool<'static>> = Vec::new();
    for (_type_name, ctor_names) in crate::constructor_registry::snapshot() {
        let present: Vec<&Dynamic<'static>> = ctor_names
            .iter()
            .filter_map(|n| base_to_dyn.get(n))
            .collect();
        if present.len() >= 2 {
            out.push(Dynamic::distinct(ctx(), &present));
        }
    }
    Ok(out)
}

// =============================================================================
// Top-level: smt_valid
// =============================================================================

#[pyfunction]
pub fn smt_valid(py: Python<'_>, constraint: PyObject) -> PyResult<bool> {
    let key = {
        let k = alpha_key(py, constraint.clone_ref(py))?;
        k
    };

    // Cache hit?
    if let Some(v) = cache().lock().unwrap().get(&key).copied() {
        return Ok(v);
    }

    let leaves = flatten(py, constraint, None)?;
    let leaves_b = leaves.bind(py);

    let solver_mutex = solver();
    let guard = solver_mutex.lock().unwrap();
    let s: &Solver<'static> = &guard.0;

    for i in 0..leaves_b.len() {
        let cc_obj = leaves_b.get_item(i)?;
        let cc = cc_obj.downcast::<CanonicConstraint>()?;
        let cc = cc.borrow();

        // Skip leaves whose conclusion is literally True.
        let smt = match translate(py, &cc)? {
            Some(b) => b,
            None => continue,
        };

        s.push();
        s.assert(&smt);
        let result = s.check();
        s.pop(1);

        match result {
            SatResult::Sat | SatResult::Unknown => {
                cache().lock().unwrap().insert(key, false);
                return Ok(false);
            }
            SatResult::Unsat => continue,
        }
    }

    cache().lock().unwrap().insert(key, true);
    Ok(true)
}
