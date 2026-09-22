pub mod outline;
pub mod problem;
pub mod prover;
pub mod task;

fn anf_deduplicate(
    formulas: Vec<problem::tptp::AnnotatedFormula>,
) -> Vec<problem::tptp::AnnotatedFormula> {
    let mut result = indexmap::IndexSet::new();
    for f in formulas {
        result.insert(f);
    }
    Vec::from_iter(result)
}
