use indexmap::IndexSet;

use crate::{
    syntax_tree::fol::sigma_0 as fol,
    translating::classical_reduction::completion::{
        atomic_formula_from, components, has_head_mismatches,
    },
};

pub mod classic;
pub mod ht;
pub mod intuitionistic;

impl fol::Theory {
    // If a theory is not completable, return None
    // Otherwise, compute CNF of theory (all intensional predicate definitions in CNF)
    // Very similar to computing completion of a completable theory
    // In the resulting theory, extensional predicates will also be in CNF
    pub(crate) fn clark_normal_form(self, intensional: &IndexSet<fol::Predicate>) -> Option<Self> {
        // Retrieve the definitions and constraints present in the theory
        let (explicit_definitions, constraints) = components(self)?;

        // Confirm there are no head mismatches
        if has_head_mismatches(&explicit_definitions) {
            return None;
        }

        // Insert explicit false definitions for missing intensional predicates
        let mut explicit_predicates = IndexSet::new();
        for formula in explicit_definitions.keys() {
            if let fol::AtomicFormula::Atom(atom) = formula {
                explicit_predicates.insert(atom.predicate());
            }
        }
        let mut definitions = explicit_definitions;
        for predicate in intensional.difference(&explicit_predicates) {
            definitions.insert(atomic_formula_from(predicate), Vec::new());
        }

        // Form Cdef for each p/n
        let cdef = definitions.into_iter().map(|(g, a)| {
            let v = g.variables();
            fol::Formula::BinaryFormula {
                connective: fol::BinaryConnective::ReverseImplication,
                lhs: fol::Formula::AtomicFormula(g).into(),
                rhs: fol::Formula::disjoin(a.into_iter().map(|f_i| {
                    let u_i = f_i.free_variables().difference(&v).cloned().collect();
                    f_i.quantify(fol::Quantifier::Exists, u_i)
                }))
                .into(),
            }
            .quantify(fol::Quantifier::Forall, v.into_iter().collect())
        });

        let mut formulas: Vec<_> = constraints
            .into_iter()
            .map(fol::Formula::universal_closure)
            .collect();
        formulas.extend(cdef);

        Some(fol::Theory { formulas })
    }

    // Completes a theory in Clark Normal Form relative to a set of intensional predicates
    // fn cnf_completion(self, intensional: IndexSet<fol::Predicate>) -> Self {
    //     let mut formulas = Vec::new();

    //     for formula in self.formulas {
    //         match formula {
    //             fol::Formula::AtomicFormula(atomic_formula) => todo!(),
    //             fol::Formula::UnaryFormula { connective, formula } => todo!(),
    //             fol::Formula::BinaryFormula { connective, lhs, rhs } => todo!(),
    //             fol::Formula::QuantifiedFormula { quantification, formula } => todo!(),
    //         }
    //     }

    //     fol::Theory{ formulas }
    // }
}

#[cfg(test)]
mod tests {
    use indexmap::IndexSet;

    use crate::syntax_tree::fol::sigma_0 as fol;

    #[test]
    fn test_clark_normal_form() {
        for (src, predicates, target) in [
            (
                "forall X (q(X) -> p(X)). forall X (r(X) -> p(X)).",
                vec!["p/1"],
                "forall X (p(X) <- q(X) or r(X)).",
            ),
            (
                "forall X (q(X) -> p(X)). forall X (r(X) -> p(X)).",
                vec!["p/1", "r/1"],
                "forall X (p(X) <- q(X) or r(X)). forall V1 (r(V1) <- #false).",
            ),
        ] {
            let intensional = IndexSet::from_iter(
                predicates
                    .into_iter()
                    .map(|p| p.parse::<fol::Predicate>().unwrap()),
            );
            let left = src
                .parse::<fol::Theory>()
                .unwrap()
                .clark_normal_form(&intensional)
                .unwrap();
            let right: fol::Theory = target.parse().unwrap();
            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }
}
