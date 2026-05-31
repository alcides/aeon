//! aeon_rs: Rust core for the Aeon programming language, exposed via PyO3.
//!
//! PR 1 scope: AST classes (Name, Kind, LiquidTerm, Type, Term hierarchies)
//! and the two hottest recursive walks (type_substitution,
//! substitution_in_liquid) ported to Rust. The Python modules
//! aeon.core.types, aeon.core.terms, aeon.core.liquid, aeon.utils.name
//! become thin re-exports of this crate.

use pyo3::prelude::*;

mod bind;
mod builders;
mod constructor_registry;
mod core_bind;
mod core_pprint;
mod decorators;
mod desugar;
mod desugar_orch;
mod elab_inst;
mod elabctx;
mod elaboration;
mod entailment;
mod evaluator;
mod helpers;
mod horn;
mod kind;
mod linearity;
mod liquefy;
mod liquid;
mod liquid_check;
mod liquid_ops;
mod loc;
mod location;
mod lowering;
mod multiplicity;
mod name;
mod normal_form;
mod partial_vc;
mod ple;
mod pprint_helpers;
mod prelude_consts;
mod qualifiers;
mod rust_enum_synth;
mod smt_ctx;
mod smt_encode;
mod smt_flatten;
mod smt_helpers;
mod smt_z3;
mod sub;
mod sugar_helpers;
mod superscripts;
mod termination;
mod typectx;
mod typeinfer;
mod well_formed;
mod substitutions;
mod sugar;
mod term_subst;
mod terms;
mod types;
mod utils_pprint;
mod vcs;

#[pymodule]
fn aeon_rs(m: &Bound<'_, PyModule>) -> PyResult<()> {
    // Name & helpers
    m.add_class::<name::Name>()?;
    m.add_class::<name::FreshCounter>()?;

    // Source locations (aeon.utils.location).
    m.add_class::<location::Location>()?;
    m.add_class::<location::FileLocation>()?;
    m.add_class::<location::SynthesizedLocation>()?;

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
    m.add_function(wrap_pyfunction!(liquid::liquid_free_vars, m)?)?;

    // Type hierarchy
    m.add_class::<types::Type>()?;
    m.add_class::<types::Top>()?;
    m.add_class::<types::TypeVar>()?;
    m.add_class::<types::AbstractionType>()?;
    m.add_class::<types::RefinedType>()?;
    m.add_class::<types::TypePolymorphism>()?;
    m.add_class::<types::RefinementPolymorphism>()?;
    m.add_class::<types::TypeConstructor>()?;
    m.add_class::<types::ExistentialType>()?;

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
    m.add_function(wrap_pyfunction!(substitutions::collect_from_term, m)?)?;
    m.add_function(wrap_pyfunction!(substitutions::substitute_vartype, m)?)?;
    m.add_function(wrap_pyfunction!(term_subst::substitute_vartype_in_term, m)?)?;
    m.add_function(wrap_pyfunction!(term_subst::substitution_liquid_in_type, m)?)?;
    m.add_function(wrap_pyfunction!(term_subst::substitution_liquid_in_term, m)?)?;
    m.add_function(wrap_pyfunction!(
        term_subst::instantiate_refinement_with_horn_in_liquid,
        m
    )?)?;
    m.add_function(wrap_pyfunction!(
        term_subst::instantiate_refinement_with_horn_in_type,
        m
    )?)?;
    m.add_function(wrap_pyfunction!(term_subst::substitution, m)?)?;

    // liquefy / inline_lets cluster
    m.add_function(wrap_pyfunction!(liquefy::inline_lets, m)?)?;
    m.add_function(wrap_pyfunction!(liquefy::liquefy, m)?)?;
    m.add_function(wrap_pyfunction!(liquefy::instantiate_refinement_in_liquid, m)?)?;
    m.add_function(wrap_pyfunction!(liquefy::instantiate_refinement_in_type, m)?)?;
    m.add_function(wrap_pyfunction!(liquefy::substitution_in_type, m)?)?;

    // Sugar (surface) AST — SType hierarchy
    m.add_class::<sugar::SType>()?;
    m.add_class::<sugar::STypeVar>()?;
    m.add_class::<sugar::SRefinedType>()?;
    m.add_class::<sugar::SAbstractionType>()?;
    m.add_class::<sugar::STypePolymorphism>()?;
    m.add_class::<sugar::SRefinementPolymorphism>()?;
    m.add_class::<sugar::STypeConstructor>()?;

    // Sugar AST — STerm hierarchy
    m.add_class::<sugar::STerm>()?;
    m.add_class::<sugar::SLiteral>()?;
    m.add_class::<sugar::SVar>()?;
    m.add_class::<sugar::SQualifiedVar>()?;
    m.add_class::<sugar::SAnnotation>()?;
    m.add_class::<sugar::SHole>()?;
    m.add_class::<sugar::SBy>()?;
    m.add_class::<sugar::SApplication>()?;
    m.add_class::<sugar::SAbstraction>()?;
    m.add_class::<sugar::SLet>()?;
    m.add_class::<sugar::SRec>()?;
    m.add_class::<sugar::SIf>()?;
    m.add_class::<sugar::SAnonConstructor>()?;
    m.add_class::<sugar::SMatchBranch>()?;
    m.add_class::<sugar::SMatch>()?;
    m.add_class::<sugar::STypeAbstraction>()?;
    m.add_class::<sugar::SRefinementAbstraction>()?;
    m.add_class::<sugar::STypeApplication>()?;
    m.add_class::<sugar::SRefinementApplication>()?;

    // Sugar AST — Node hierarchy
    m.add_class::<sugar::Node>()?;
    m.add_class::<sugar::ImportAe>()?;
    m.add_class::<sugar::TypeDecl>()?;
    m.add_class::<sugar::InductiveDecl>()?;
    m.add_class::<sugar::Decorator>()?;
    m.add_class::<sugar::Definition>()?;
    m.add_class::<sugar::Program>()?;

    // SMT encoder — z3-free slices
    m.add_function(wrap_pyfunction!(ple::ple_unfold_fixpoint, m)?)?;
    m.add_function(wrap_pyfunction!(smt_helpers::unrefine_type, m)?)?;
    m.add_function(wrap_pyfunction!(smt_helpers::uncurry, m)?)?;

    // Verification conditions (vcs) — Constraint hierarchy + alpha_key
    m.add_class::<vcs::Constraint>()?;
    m.add_class::<vcs::LiquidConstraint>()?;
    m.add_class::<vcs::Conjunction>()?;
    m.add_class::<vcs::UninterpretedFunctionDeclaration>()?;
    m.add_class::<vcs::ReflectedFunctionDeclaration>()?;
    m.add_class::<vcs::Implication>()?;
    m.add_class::<vcs::TypeVarDeclaration>()?;
    m.add_function(wrap_pyfunction!(vcs::alpha_key, m)?)?;
    m.add_function(wrap_pyfunction!(vcs::variables_in_liq, m)?)?;
    m.add_function(wrap_pyfunction!(vcs::variables_free_in, m)?)?;

    // SMT encoder — pure flatten helpers (still z3-free)
    m.add_function(wrap_pyfunction!(smt_encode::specialize_liquid_term, m)?)?;
    m.add_function(wrap_pyfunction!(smt_encode::rename_constraint, m)?)?;

    // SMT encoder — flatten + the SMTContext / CanonicConstraint pyclasses.
    m.add_class::<smt_ctx::SMTContext>()?;
    m.add_class::<smt_ctx::CanonicConstraint>()?;
    m.add_function(wrap_pyfunction!(smt_flatten::flatten, m)?)?;

    // SMT solver — native z3 layer (no z3-py).
    m.add_function(wrap_pyfunction!(smt_z3::smt_valid, m)?)?;

    // Inductive constructor registry (aeon.verification.constructor_registry).
    m.add_function(wrap_pyfunction!(constructor_registry::register_constructors, m)?)?;
    m.add_function(wrap_pyfunction!(constructor_registry::get_constructor_groups, m)?)?;
    m.add_function(wrap_pyfunction!(constructor_registry::clear_constructor_registry, m)?)?;

    // Subtyping — constraint generation (aeon.verification.sub).
    m.add_function(wrap_pyfunction!(sub::ensure_refined, m)?)?;
    m.add_function(wrap_pyfunction!(sub::is_first_order_function, m)?)?;
    m.add_function(wrap_pyfunction!(sub::lower_constraint_type, m)?)?;
    m.add_function(wrap_pyfunction!(sub::implication_constraint, m)?)?;
    m.add_function(wrap_pyfunction!(sub::sub, m)?)?;

    // Constraint helpers — simplification, CNF, pretty-print
    // (aeon.verification.helpers).
    m.add_function(wrap_pyfunction!(helpers::constraint_location, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::imp, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::end, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::conj, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::constraint_builder, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::simplify_expr, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::simplify_is_true, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::flatten_conjunctions, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::is_used_liquid, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::is_used, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::constraint_free_variables, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::substitution_in_constraint, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::used_variables, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::simplify_constraint, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::simplify_constraint_fixpoint, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::conjunctive_normal_form, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::split_or_disjuncts, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::split_or_in_conclusion, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::is_implication_true, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::remove_unrelated_context, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::reduce_to_useful_constraint, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::pretty_print_constraint, m)?)?;
    m.add_function(wrap_pyfunction!(helpers::show_constraint, m)?)?;

    // Horn-clause solver (aeon.verification.horn).
    m.add_function(wrap_pyfunction!(horn::smt_base_type, m)?)?;
    m.add_function(wrap_pyfunction!(horn::fresh, m)?)?;
    m.add_function(wrap_pyfunction!(horn::obtain_holes, m)?)?;
    m.add_function(wrap_pyfunction!(horn::obtain_holes_constraint, m)?)?;
    m.add_function(wrap_pyfunction!(horn::contains_horn, m)?)?;
    m.add_function(wrap_pyfunction!(horn::contains_horn_constraint, m)?)?;
    m.add_function(wrap_pyfunction!(horn::wellformed_horn, m)?)?;
    m.add_function(wrap_pyfunction!(horn::get_possible_args, m)?)?;
    m.add_function(wrap_pyfunction!(horn::mk_arg, m)?)?;
    m.add_function(wrap_pyfunction!(horn::merge_assignments, m)?)?;
    m.add_function(wrap_pyfunction!(horn::split, m)?)?;
    m.add_function(wrap_pyfunction!(horn::has_k_head, m)?)?;
    m.add_function(wrap_pyfunction!(horn::flat, m)?)?;
    m.add_function(wrap_pyfunction!(horn::fill_horn_arguments, m)?)?;
    m.add_function(wrap_pyfunction!(horn::apply_liquid, m)?)?;
    m.add_function(wrap_pyfunction!(horn::apply_constraint, m)?)?;
    m.add_function(wrap_pyfunction!(horn::apply, m)?)?;
    m.add_function(wrap_pyfunction!(horn::extract_components_of_imp, m)?)?;
    m.add_function(wrap_pyfunction!(horn::weaken, m)?)?;
    m.add_function(wrap_pyfunction!(horn::fixpoint, m)?)?;
    m.add_function(wrap_pyfunction!(horn::build_initial_assignment, m)?)?;
    m.add_function(wrap_pyfunction!(horn::adapt_qualifier_to_hole, m)?)?;
    m.add_function(wrap_pyfunction!(horn::build_qualifier_candidates, m)?)?;
    m.add_function(wrap_pyfunction!(horn::solve, m)?)?;

    // Typing context (aeon.typechecking.context).
    m.add_class::<typectx::TypingContextEntry>()?;
    m.add_class::<typectx::VariableBinder>()?;
    m.add_class::<typectx::UninterpretedBinder>()?;
    m.add_class::<typectx::ReflectedBinder>()?;
    m.add_class::<typectx::TypeBinder>()?;
    m.add_class::<typectx::TypeConstructorBinder>()?;
    m.add_class::<typectx::TypingContext>()?;

    // Qualifier extraction (aeon.typechecking.qualifiers).
    m.add_function(wrap_pyfunction!(qualifiers::extract_qualifier_atoms, m)?)?;

    // Runtime evaluator (aeon.backend.evaluator).
    m.add_class::<evaluator::EvaluationContext>()?;
    m.add_class::<evaluator::Closure>()?;
    m.add_function(wrap_pyfunction!(evaluator::eval, m)?)?;

    // Well-formedness (aeon.typechecking.well_formed).
    m.add_function(wrap_pyfunction!(well_formed::py_wellformed, m)?)?;

    // Entailment (aeon.typechecking.entailment).
    m.add_function(wrap_pyfunction!(entailment::entailment, m)?)?;
    m.add_function(wrap_pyfunction!(entailment::entailment_context, m)?)?;

    // Termination metric constraints (aeon.typechecking.termination).
    m.add_function(wrap_pyfunction!(termination::termination_metric_constraints, m)?)?;
    m.add_function(wrap_pyfunction!(termination::py_lexicographic_less, m)?)?;
    m.add_function(wrap_pyfunction!(termination::py_liquefy_metric_at, m)?)?;
    m.add_function(wrap_pyfunction!(termination::collect_recursive_calls_with_paths_py, m)?)?;
    m.add_function(wrap_pyfunction!(termination::entry_refinement_liquids_py, m)?)?;
    m.add_function(wrap_pyfunction!(termination::peel_abstractions_py, m)?)?;
    m.add_function(wrap_pyfunction!(termination::peel_application_chain_py, m)?)?;
    m.add_function(wrap_pyfunction!(termination::peel_type_formal_names_py, m)?)?;
    m.add_function(wrap_pyfunction!(termination::substitute_formals_py, m)?)?;

    // Linearity / QTT (aeon.typechecking.linearity).
    m.add_function(wrap_pyfunction!(linearity::check_linearity, m)?)?;

    // Type inference (aeon.typechecking.typeinfer).
    m.add_function(wrap_pyfunction!(typeinfer::synth, m)?)?;
    m.add_function(wrap_pyfunction!(typeinfer::check, m)?)?;
    m.add_function(wrap_pyfunction!(typeinfer::check_type, m)?)?;
    m.add_function(wrap_pyfunction!(typeinfer::constraint_to_parts, m)?)?;
    m.add_function(wrap_pyfunction!(typeinfer::check_type_errors, m)?)?;
    m.add_function(wrap_pyfunction!(typeinfer::py_is_compatible, m)?)?;
    m.add_function(wrap_pyfunction!(typeinfer::py_reflected_impl_for, m)?)?;

    // Sugar AST helpers (aeon.sugar.{equality, lifting, substitutions}).
    m.add_function(wrap_pyfunction!(sugar_helpers::type_equality, m)?)?;
    m.add_function(wrap_pyfunction!(sugar_helpers::term_equality, m)?)?;
    m.add_function(wrap_pyfunction!(sugar_helpers::lift_liquid, m)?)?;
    m.add_function(wrap_pyfunction!(sugar_helpers::lift_type, m)?)?;
    m.add_function(wrap_pyfunction!(sugar_helpers::lift, m)?)?;
    m.add_function(wrap_pyfunction!(sugar_helpers::normalize, m)?)?;
    m.add_function(wrap_pyfunction!(sugar_helpers::substitute_svartype_in_stype, m)?)?;
    m.add_function(wrap_pyfunction!(sugar_helpers::substitution_sterm_in_stype, m)?)?;
    m.add_function(wrap_pyfunction!(sugar_helpers::substitution_sterm_in_sterm, m)?)?;
    m.add_function(wrap_pyfunction!(sugar_helpers::substitute_refinement_param_in_stype, m)?)?;
    m.add_function(wrap_pyfunction!(sugar_helpers::substitution_svartype_in_sterm, m)?)?;

    // Partial VC builder (aeon.typechecking.partial_vc).
    m.add_class::<partial_vc::ModularVC>()?;
    m.add_function(wrap_pyfunction!(partial_vc::build_modular_vc, m)?)?;

    // Elaboration typing context (aeon.elaboration.context).
    m.add_class::<elabctx::ElabTypingContextEntry>()?;
    m.add_class::<elabctx::ElabVariableBinder>()?;
    m.add_class::<elabctx::ElabUninterpretedBinder>()?;
    m.add_class::<elabctx::ElabTypeVarBinder>()?;
    m.add_class::<elabctx::ElabTypeDecl>()?;
    m.add_class::<elabctx::ElaborationTypingContext>()?;
    m.add_function(wrap_pyfunction!(elabctx::build_typing_context, m)?)?;

    // Elaboration instantiation (sugar-level) (aeon.elaboration.instantiation).
    m.add_function(wrap_pyfunction!(elab_inst::sugar_type_substitution, m)?)?;
    m.add_function(wrap_pyfunction!(elab_inst::sugar_type_variable_instantiation, m)?)?;

    // Elaboration algorithm (aeon.elaboration.__init__).
    m.add_class::<elaboration::UnificationVar>()?;
    m.add_class::<elaboration::Union>()?;
    m.add_class::<elaboration::Intersection>()?;
    m.add_function(wrap_pyfunction!(elaboration::elaborate_foralls, m)?)?;
    m.add_function(wrap_pyfunction!(elaboration::py_elaborate_check, m)?)?;
    m.add_function(wrap_pyfunction!(elaboration::py_elaborate_remove_unification, m)?)?;
    m.add_function(wrap_pyfunction!(elaboration::elaborate, m)?)?;

    // Name-resolution binding pass (aeon.sugar.bind).
    m.add_function(wrap_pyfunction!(bind::bind, m)?)?;
    m.add_function(wrap_pyfunction!(bind::bind_program, m)?)?;
    m.add_function(wrap_pyfunction!(bind::py_bind_sterm, m)?)?;
    m.add_function(wrap_pyfunction!(bind::py_bind_stype, m)?)?;
    m.add_function(wrap_pyfunction!(bind::py_bind_ectx, m)?)?;

    // Sugar → Core lowering (aeon.sugar.lowering).
    m.add(
        "LoweringException",
        m.py().get_type_bound::<lowering::LoweringException>(),
    )?;
    m.add(
        "LiquefactionException",
        m.py().get_type_bound::<lowering::LiquefactionException>(),
    )?;
    m.add_function(wrap_pyfunction!(lowering::liquefy, m)?)?;
    m.add_function(wrap_pyfunction!(lowering::type_to_core, m)?)?;
    m.add_function(wrap_pyfunction!(lowering::lower_to_core, m)?)?;
    m.add_function(wrap_pyfunction!(lowering::lower_to_core_context, m)?)?;

    // QTT multiplicity (aeon.core.multiplicity).
    m.add_class::<multiplicity::Multiplicity>()?;
    m.add("M0", multiplicity::m0(m.py()))?;
    m.add("M1", multiplicity::m1(m.py()))?;
    m.add("MOmega", multiplicity::momega(m.py()))?;
    m.add("MN", multiplicity::mn(m.py()))?;
    m.add_function(wrap_pyfunction!(multiplicity::add, m)?)?;
    m.add_function(wrap_pyfunction!(multiplicity::mul, m)?)?;
    m.add_function(wrap_pyfunction!(multiplicity::multiplicity_from_token, m)?)?;

    // Liquid operator prelude / smart constructors (aeon.core.liquid_ops).
    m.add("liquid_prelude", liquid_ops::get_liquid_prelude(m.py()))?;
    m.add_function(wrap_pyfunction!(liquid_ops::mk_liquid_and, m)?)?;
    m.add_function(wrap_pyfunction!(liquid_ops::mk_liquid_or, m)?)?;

    // ANF / partial-evaluation pass (aeon.optimization.normal_form).
    m.add_function(wrap_pyfunction!(normal_form::normal_form, m)?)?;
    m.add_function(wrap_pyfunction!(normal_form::optimize, m)?)?;
    m.add_function(wrap_pyfunction!(normal_form::py_nf, m)?)?;

    // Core-level name-resolution binding pass (aeon.core.bind).
    m.add_function(wrap_pyfunction!(core_bind::bind_ids, m)?)?;
    m.add_function(wrap_pyfunction!(core_bind::py_bind_lq, m)?)?;
    m.add_function(wrap_pyfunction!(core_bind::py_bind_type, m)?)?;
    m.add_function(wrap_pyfunction!(core_bind::py_bind_term, m)?)?;
    m.add_function(wrap_pyfunction!(core_bind::py_bind_ctx, m)?)?;

    // Core pretty-printer (aeon.core.pprint).
    m.add(
        "aeon_prelude_ops_to_text",
        core_pprint::get_aeon_prelude_ops_to_text(m.py()),
    )?;
    m.add_function(wrap_pyfunction!(core_pprint::pretty_print, m)?)?;
    m.add_function(wrap_pyfunction!(core_pprint::pretty_print_term, m)?)?;
    m.add_function(wrap_pyfunction!(core_pprint::py_operator_name, m)?)?;
    m.add_function(wrap_pyfunction!(core_pprint::custom_preludes_ops_representation, m)?)?;

    // Pretty-printer (aeon.utils.pprint_helpers).
    m.add_class::<pprint_helpers::Doc>()?;
    m.add_function(wrap_pyfunction!(pprint_helpers::nil, m)?)?;
    m.add_function(wrap_pyfunction!(pprint_helpers::text, m)?)?;
    m.add_function(wrap_pyfunction!(pprint_helpers::line, m)?)?;
    m.add_function(wrap_pyfunction!(pprint_helpers::soft_line, m)?)?;
    m.add_function(wrap_pyfunction!(pprint_helpers::hard_line, m)?)?;
    m.add_function(wrap_pyfunction!(pprint_helpers::nest, m)?)?;
    m.add_function(wrap_pyfunction!(pprint_helpers::group, m)?)?;
    m.add_function(wrap_pyfunction!(pprint_helpers::parens, m)?)?;
    m.add_function(wrap_pyfunction!(pprint_helpers::concat, m)?)?;
    m.add_function(wrap_pyfunction!(pprint_helpers::insert_between, m)?)?;
    m.add("DEFAULT_WIDTH", pprint_helpers::DEFAULT_WIDTH)?;
    m.add("DEFAULT_TAB_SIZE", pprint_helpers::DEFAULT_TAB_SIZE)?;

    // Pretty-printer (aeon.utils.pprint).
    m.add_class::<utils_pprint::Operation>()?;
    m.add_class::<utils_pprint::Precedence>()?;
    m.add_class::<utils_pprint::Associativity>()?;
    m.add_class::<utils_pprint::Side>()?;
    m.add_class::<utils_pprint::ParenthesisContext>()?;
    m.add_function(wrap_pyfunction!(utils_pprint::needs_parens_aux, m)?)?;
    m.add_function(wrap_pyfunction!(utils_pprint::needs_parens, m)?)?;
    m.add_function(wrap_pyfunction!(utils_pprint::stype_pretty, m)?)?;
    m.add_function(wrap_pyfunction!(utils_pprint::sterm_pretty, m)?)?;
    m.add_function(wrap_pyfunction!(utils_pprint::node_pretty, m)?)?;
    m.add_function(wrap_pyfunction!(utils_pprint::pretty_print_sterm, m)?)?;
    m.add_function(wrap_pyfunction!(utils_pprint::pretty_print_node, m)?)?;
    m.add_function(wrap_pyfunction!(utils_pprint::normalize_term_py, m)?)?;
    m.add_function(wrap_pyfunction!(utils_pprint::simplify_sterm_py, m)?)?;

    // Sugar desugaring (algorithmic core of aeon.sugar.desugar).
    m.add_class::<desugar::DesugaredProgram>()?;
    m.add_function(wrap_pyfunction!(desugar::definition_with_inferred_decreasing, m)?)?;
    m.add_function(wrap_pyfunction!(desugar::lower_by_blocks_in_sterm, m)?)?;
    m.add_function(wrap_pyfunction!(desugar::lower_by_blocks_in_definitions, m)?)?;
    m.add_function(wrap_pyfunction!(desugar::resolve_qualified_names_in_sterm, m)?)?;
    m.add_function(wrap_pyfunction!(desugar::resolve_qualified_names_in_stype, m)?)?;
    m.add_function(wrap_pyfunction!(desugar::resolve_qualified_names_in_definition, m)?)?;
    m.add_function(wrap_pyfunction!(desugar::determine_main_function, m)?)?;
    m.add_function(wrap_pyfunction!(desugar::type_of_definition, m)?)?;
    m.add_function(wrap_pyfunction!(desugar::convert_definition_to_srec, m)?)?;
    m.add_function(wrap_pyfunction!(desugar::update_program_and_context, m)?)?;
    m.add_function(wrap_pyfunction!(desugar::replace_concrete_types, m)?)?;
    m.add_function(wrap_pyfunction!(desugar::introduce_forall_in_types, m)?)?;
    m.add_function(wrap_pyfunction!(desugar::introduce_rforall_in_types, m)?)?;
    m.add_function(wrap_pyfunction!(desugar::infer_inductive_rforall_decls, m)?)?;
    m.add_function(wrap_pyfunction!(desugar::expand_inductive_decls, m)?)?;
    m.add_function(wrap_pyfunction!(desugar::lower_match_to_inductive_rec, m)?)?;

    // Sugar desugaring orchestrator (top-level + import resolver +
    // decorator macro pass; aeon.sugar.desugar's residual Python).
    m.add_function(wrap_pyfunction!(desugar_orch::desugar, m)?)?;
    m.add_function(wrap_pyfunction!(desugar_orch::py_handle_imports, m)?)?;
    m.add_function(wrap_pyfunction!(desugar_orch::py_resolve_import, m)?)?;
    m.add_function(wrap_pyfunction!(desugar_orch::py_is_native_import_def, m)?)?;
    m.add_function(wrap_pyfunction!(desugar_orch::py_bare_name, m)?)?;
    m.add_function(wrap_pyfunction!(desugar_orch::apply_decorators_in_definitions, m)?)?;
    m.add_function(wrap_pyfunction!(desugar_orch::apply_decorators_in_program, m)?)?;
    m.add_function(wrap_pyfunction!(desugar_orch::clear_import_cache, m)?)?;

    // Static prelude constants — operator-name lists and native_types
    // (aeon.prelude.prelude). The Python lambdas and the
    // typing_vars/evaluation_vars dicts stay in Python.
    m.add(
        "INTEGER_ARITHMETIC_OPERATORS",
        prelude_consts::get_integer_arithmetic_operators(m.py()),
    )?;
    m.add(
        "COMPARISON_OPERATORS",
        prelude_consts::get_comparison_operators(m.py()),
    )?;
    m.add("LOGICAL_OPERATORS", prelude_consts::get_logical_operators(m.py()))?;
    m.add("EQUALITY_OPERATORS", prelude_consts::get_equality_operators(m.py()))?;
    m.add("ALL_OPS", prelude_consts::get_all_ops(m.py()))?;
    m.add("native_types", prelude_consts::get_native_types(m.py()))?;

    // Superscript / subscript translation (aeon.utils.superscripts).
    m.add_function(wrap_pyfunction!(superscripts::superscript, m)?)?;
    m.add_function(wrap_pyfunction!(superscripts::subscript, m)?)?;

    // Random-enumerative synthesizer with Pareto-front tracking.
    m.add_class::<rust_enum_synth::RustEnumSynthesizer>()?;

    // Decorator infrastructure (aeon.decorators).
    m.add_function(wrap_pyfunction!(decorators::metadata_update, m)?)?;
    m.add_function(wrap_pyfunction!(decorators::metadata_update_by_name, m)?)?;
    m.add_function(wrap_pyfunction!(decorators::apply_decorators, m)?)?;
    m.add_function(wrap_pyfunction!(decorators::collect_core_decorator_queue, m)?)?;
    m.add_function(wrap_pyfunction!(decorators::apply_core_decorators_phase, m)?)?;
    m.add(
        "CORE_DECORATOR_QUEUE_META_KEY",
        decorators::get_core_decorator_queue_meta_key(m.py()),
    )?;

    // Liquid (refinement) type checker (aeon.typechecking.liquid).
    m.add(
        "LiquidTypeCheckException",
        m.py().get_type_bound::<liquid_check::LiquidTypeCheckException>(),
    )?;
    m.add_class::<liquid_check::LiquidTypeCheckingContext>()?;
    m.add_function(wrap_pyfunction!(liquid_check::lower_abstraction_type, m)?)?;
    m.add_function(wrap_pyfunction!(liquid_check::lower_context, m)?)?;
    m.add_function(wrap_pyfunction!(liquid_check::type_infer_liquid, m)?)?;
    m.add_function(wrap_pyfunction!(liquid_check::check_liquid, m)?)?;
    m.add_function(wrap_pyfunction!(liquid_check::typecheck_liquid, m)?)?;

    Ok(())
}
