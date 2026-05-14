//! aeon_rs: Rust core for the Aeon programming language, exposed via PyO3.
//!
//! PR 1 scope: AST classes (Name, Kind, LiquidTerm, Type, Term hierarchies)
//! and the two hottest recursive walks (type_substitution,
//! substitution_in_liquid) ported to Rust. The Python modules
//! aeon.core.types, aeon.core.terms, aeon.core.liquid, aeon.utils.name
//! become thin re-exports of this crate.

use pyo3::prelude::*;

mod kind;
mod liquid;
mod loc;
mod name;
mod substitutions;
mod terms;
mod types;

#[pymodule]
fn aeon_rs(m: &Bound<'_, PyModule>) -> PyResult<()> {
    // Name & helpers
    m.add_class::<name::Name>()?;
    m.add_class::<name::FreshCounter>()?;

    // Kind hierarchy
    m.add_class::<kind::Kind>()?;
    m.add_class::<kind::BaseKind>()?;
    m.add_class::<kind::StarKind>()?;

    // LiquidTerm hierarchy
    m.add_class::<liquid::LiquidTerm>()?;
    m.add_class::<liquid::LiquidHole>()?;
    m.add_class::<liquid::LiquidLiteralBool>()?;
    m.add_class::<liquid::LiquidLiteralInt>()?;
    m.add_class::<liquid::LiquidLiteralFloat>()?;
    m.add_class::<liquid::LiquidLiteralString>()?;
    m.add_class::<liquid::LiquidVar>()?;
    m.add_class::<liquid::LiquidApp>()?;
    m.add_class::<liquid::LiquidHornApplication>()?;

    // Type hierarchy
    m.add_class::<types::Type>()?;
    m.add_class::<types::Top>()?;
    m.add_class::<types::TypeVar>()?;
    m.add_class::<types::AbstractionType>()?;
    m.add_class::<types::RefinedType>()?;
    m.add_class::<types::TypePolymorphism>()?;
    m.add_class::<types::RefinementPolymorphism>()?;
    m.add_class::<types::TypeConstructor>()?;

    // Term hierarchy
    m.add_class::<terms::Term>()?;
    m.add_class::<terms::Literal>()?;
    m.add_class::<terms::Var>()?;
    m.add_class::<terms::Annotation>()?;
    m.add_class::<terms::Hole>()?;
    m.add_class::<terms::Application>()?;
    m.add_class::<terms::Abstraction>()?;
    m.add_class::<terms::Let>()?;
    m.add_class::<terms::Rec>()?;
    m.add_class::<terms::If>()?;
    m.add_class::<terms::TypeAbstraction>()?;
    m.add_class::<terms::RefinementAbstraction>()?;
    m.add_class::<terms::TypeApplication>()?;
    m.add_class::<terms::RefinementApplication>()?;

    // Ported recursive walks
    m.add_function(wrap_pyfunction!(substitutions::type_substitution, m)?)?;
    m.add_function(wrap_pyfunction!(substitutions::type_variable_instantiation, m)?)?;
    m.add_function(wrap_pyfunction!(substitutions::substitution_in_liquid, m)?)?;
    m.add_function(wrap_pyfunction!(substitutions::refined_to_unrefined_type, m)?)?;
    m.add_function(wrap_pyfunction!(substitutions::collect_from_type, m)?)?;

    Ok(())
}
