use crate::{
    syntax_tree::fol::sigma_0 as fol,
    translating::classical_reduction::completion::{components, has_head_mismatches},
};

pub mod classic;
pub mod ht;
pub mod intuitionistic;

impl fol::Theory {
    // If a theory is not completable, return None
    // Otherwise, compute CNF of theory (all intensional predicate definitions in CNF)
    // But actually this method does more than that, because extensional predicates will also be in CNF
    fn clark_normal_form(self) -> Option<Self> {
        // Retrieve the definitions and constraints present in the theory
        let (explicit_definitions, constraints) = components(self)?;

        // Confirm there are no head mismatches
        if has_head_mismatches(&explicit_definitions) {
            return None;
        }

        let completed_definitions = explicit_definitions.into_iter().map(|(g, a)| {
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
        formulas.extend(completed_definitions);

        Some(fol::Theory { formulas })
    }
}

#[cfg(test)]
mod tests {
    use crate::syntax_tree::fol::sigma_0 as fol;

    #[test]
        fn test_clark_normal_form() {
            for (src, target) in [
                ("forall X (q(X) -> p(X)). forall X (r(X) -> p(X)).", "forall X (p(X) <- q(X) or r(X))."),
            ] {
                let left= src.parse::<fol::Theory>().unwrap().clark_normal_form().unwrap();
                let right: fol::Theory = target.parse().unwrap();
                assert!(
                    left == right,
                    "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
                );
            }
        }
}
