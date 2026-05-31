//! Minimum viable Rust port of aeon.core.instantiation.type_substitution.
//!
//! Equivalent of the recursive Type walk in pure Rust. Refinements (LiquidTerm)
//! are kept opaque (untouched payload) — matches the common case where
//! alpha is substituted with a TypeConstructor, so refinements pass through.
//! This is the dominant shape during synthesis (we observed it via cProfile).
//!
//! The benchmark function builds a representative balanced tree, runs
//! type_substitution N times, and returns elapsed seconds.

use pyo3::prelude::*;
use std::sync::Arc;
use std::time::Instant;

#[derive(Clone, Debug)]
struct RName {
    name: Arc<str>,
    id: i64,
}

impl PartialEq for RName {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id && self.name == other.name
    }
}

#[derive(Clone, Debug)]
enum RType {
    Top,
    TypeVar(RName),
    Abstraction { var_name: RName, var_type: Arc<RType>, body: Arc<RType> },
    Refined { name: RName, inner: Arc<RType>, /* refinement: opaque, not touched */ },
    TypePolymorphism { name: RName, body: Arc<RType> },
    Constructor { name: RName, args: Vec<Arc<RType>> },
}

fn type_substitution_rs(t: &Arc<RType>, alpha: &RName, beta: &Arc<RType>) -> Arc<RType> {
    match t.as_ref() {
        RType::TypeVar(n) => {
            if n == alpha {
                beta.clone()
            } else {
                t.clone()
            }
        }
        RType::Top => t.clone(),
        RType::Abstraction { var_name, var_type, body } => Arc::new(RType::Abstraction {
            var_name: var_name.clone(),
            var_type: type_substitution_rs(var_type, alpha, beta),
            body: type_substitution_rs(body, alpha, beta),
        }),
        RType::Refined { name, inner } => {
            // Common case: inner has no nested refinement to merge.
            // We replicate the pass-through branch of the Python implementation
            // (the refinement-merging branch only fires when inner becomes a
            // RefinedType after substitution; we keep refinements opaque).
            Arc::new(RType::Refined {
                name: name.clone(),
                inner: type_substitution_rs(inner, alpha, beta),
            })
        }
        RType::TypePolymorphism { name, body } => {
            if name == alpha {
                t.clone()
            } else {
                Arc::new(RType::TypePolymorphism { name: name.clone(), body: type_substitution_rs(body, alpha, beta) })
            }
        }
        RType::Constructor { name, args } => {
            let new_args: Vec<Arc<RType>> = args.iter().map(|a| type_substitution_rs(a, alpha, beta)).collect();
            Arc::new(RType::Constructor { name: name.clone(), args: new_args })
        }
    }
}

/// Build a realistic Aeon Type tree.
/// RefinedType.inner is restricted to TypeConstructor|TypeVar (matches Aeon invariant).
fn build_tree(depth: u32, fanout: u32) -> Arc<RType> {
    if depth == 0 {
        // leaf: a refined base type, the most common shape in real code
        let base = Arc::new(RType::Constructor {
            name: RName { name: Arc::from("Int"), id: 0 },
            args: vec![],
        });
        Arc::new(RType::Refined {
            name: RName { name: Arc::from("v"), id: 0 },
            inner: base,
        })
    } else if depth % 2 == 0 {
        // Constructor with fanout children — like (List a), (Map K V)
        let mut args = Vec::with_capacity(fanout as usize);
        for i in 0..fanout {
            if i == 0 {
                args.push(Arc::new(RType::TypeVar(RName { name: Arc::from("a"), id: 0 })));
            } else {
                args.push(build_tree(depth - 1, fanout));
            }
        }
        Arc::new(RType::Constructor { name: RName { name: Arc::from("C"), id: depth as i64 }, args })
    } else {
        // Abstraction — function type
        Arc::new(RType::Abstraction {
            var_name: RName { name: Arc::from("x"), id: depth as i64 },
            var_type: build_tree(depth - 1, fanout),
            body: build_tree(depth - 1, fanout),
        })
    }
}

#[pyfunction]
fn bench_rust(depth: u32, fanout: u32, iters: u64) -> f64 {
    let tree = build_tree(depth, fanout);
    let alpha = RName { name: Arc::from("a"), id: 0 };
    let beta = Arc::new(RType::Constructor {
        name: RName { name: Arc::from("Int"), id: 0 },
        args: vec![],
    });
    // Warmup
    for _ in 0..10 {
        let _ = type_substitution_rs(&tree, &alpha, &beta);
    }
    let start = Instant::now();
    let mut sink = tree.clone();
    for _ in 0..iters {
        sink = type_substitution_rs(&sink, &alpha, &beta);
        // Reset so we don't accumulate (otherwise after 1 iter alpha is gone)
        sink = tree.clone();
    }
    // Use sink so the optimizer can't elide work.
    let _ = sink;
    start.elapsed().as_secs_f64()
}

/// Time only the substitution loop on a freshly built tree, no clone-in-loop overhead.
#[pyfunction]
fn bench_rust_loop(depth: u32, fanout: u32, iters: u64) -> f64 {
    let tree = build_tree(depth, fanout);
    let alpha = RName { name: Arc::from("a"), id: 0 };
    let beta = Arc::new(RType::Constructor {
        name: RName { name: Arc::from("Int"), id: 0 },
        args: vec![],
    });
    for _ in 0..10 {
        let _ = type_substitution_rs(&tree, &alpha, &beta);
    }
    let start = Instant::now();
    let mut acc: u64 = 0;
    for _ in 0..iters {
        let r = type_substitution_rs(&tree, &alpha, &beta);
        // Use r so it's not elided.
        acc = acc.wrapping_add(Arc::strong_count(&r) as u64);
    }
    let elapsed = start.elapsed().as_secs_f64();
    if acc == u64::MAX {
        println!("unreachable");
    }
    elapsed
}

/// Count nodes — gives us tree size for the report.
fn count_nodes(t: &Arc<RType>) -> u64 {
    match t.as_ref() {
        RType::Top | RType::TypeVar(_) => 1,
        RType::Abstraction { var_type, body, .. } => 1 + count_nodes(var_type) + count_nodes(body),
        RType::Refined { inner, .. } => 1 + count_nodes(inner),
        RType::TypePolymorphism { body, .. } => 1 + count_nodes(body),
        RType::Constructor { args, .. } => 1 + args.iter().map(count_nodes).sum::<u64>(),
    }
}

#[pyfunction]
fn tree_size(depth: u32, fanout: u32) -> u64 {
    count_nodes(&build_tree(depth, fanout))
}

#[pymodule]
fn aeon_rust_spike(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(bench_rust, m)?)?;
    m.add_function(wrap_pyfunction!(bench_rust_loop, m)?)?;
    m.add_function(wrap_pyfunction!(tree_size, m)?)?;
    Ok(())
}
