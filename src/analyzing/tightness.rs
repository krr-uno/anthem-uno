use {
    crate::{
        convenience::{
            unbox::{Unbox, fol::sigma_0::UnboxedFormula},
            visualizing::formula_trees::{
                FolNode, FolNodePrimitive, ancestors, grow_tree_from_formula, leafs, left_child,
            },
        },
        syntax_tree::{asp::mini_gringo as asp, fol::sigma_0 as fol},
    },
    indexmap::IndexSet,
    petgraph::{
        algo::{has_path_connecting, is_cyclic_directed},
        graph::DiGraph,
    },
    std::collections::HashMap,
};

impl fol::Formula {
    fn contains_positive_nonnegated_occurrence(&self, predicate: &fol::Predicate) -> bool {
        // TODO: Convert every `F -> false` into `not F` and every `F <- G` into `G -> F`

        // 1. An occurrence of a predicate is negated if it has an ancestor who is `not`
        // 2. Add 1 to the count for every `not` ancestor, every `<->` ancestor, and every `->` ancestor when occurrence is left child

        // every occurrence of a predicate occurs in a leaf node
        // iterate through leaf nodes, check ancestors

        let mut flag = false;

        let (_, tree) = grow_tree_from_formula(self.clone());

        for index in leafs(&tree) {
            if let FolNode {
                primitive: FolNodePrimitive::Atomic,
                content,
            } = tree[index].clone()
            {
                if let fol::AtomicFormula::Atom(atom) = content.parse().unwrap() {
                    if atom.predicate() == *predicate {
                        let mut negated = false;
                        let mut positive_count = 0;

                        for a in ancestors(&tree, index) {
                            let ancestor = tree[a].clone();
                            match ancestor.primitive {
                                FolNodePrimitive::Implication => {
                                    // Ensure index occurs in lhs subtree (antecedent) of ancestor
                                    let lhs = left_child(&tree, a);
                                    if has_path_connecting(&tree, lhs, index, None) {
                                        positive_count += 1;
                                    }
                                }
                                FolNodePrimitive::Equivalence => {
                                    positive_count += 1;
                                }
                                FolNodePrimitive::Negation => {
                                    negated = true;
                                    positive_count += 1;
                                }
                                _ => (),
                            }
                        }

                        if (!negated && positive_count % 2 == 0) {
                            flag = true;
                        }
                    }
                }
            }
        }

        flag
    }
}

pub trait Tightness {
    fn is_tight(&self, intensional_predicates: IndexSet<asp::Predicate>) -> bool;
}

impl Tightness for asp::Program {
    fn is_tight(&self, intensional_predicates: IndexSet<asp::Predicate>) -> bool {
        // TODO: is this check necessary?
        assert!(
            self.predicates().is_subset(&intensional_predicates)
                && self.predicates().is_superset(&intensional_predicates)
        );

        let mut dependency_graph = DiGraph::<(), ()>::new();
        let mut mapping = HashMap::new();

        for predicate in intensional_predicates {
            let node = dependency_graph.add_node(());
            mapping.insert(predicate, node);
        }

        for rule in &self.rules {
            if let Some(head_predicate) = rule.head.predicate() {
                for positive_body_predicate in rule.body.positive_predicates() {
                    dependency_graph.update_edge(
                        mapping[&head_predicate],
                        mapping[&positive_body_predicate],
                        (),
                    );
                }
            }
        }

        !is_cyclic_directed(&dependency_graph)
    }
}

impl Tightness for fol::Theory {
    // This definition of tightness is defined for theories in Clark Normal Form
    fn is_tight(&self, intensional_predicates: IndexSet<asp::Predicate>) -> bool {
        let intensional =
            IndexSet::from_iter(intensional_predicates.iter().map(|p| p.clone().into()));
        match self.clone().clark_normal_form(&intensional) {
            Some(theory) => {
                let mut dependency_graph = DiGraph::<(), ()>::new();
                let mut mapping = HashMap::new();

                // Add intensional predicates as vertices
                for predicate in intensional.iter() {
                    let node = dependency_graph.add_node(());
                    mapping.insert(predicate.clone(), node);
                }

                // Add edge (p,q) if theory contains a formula `forall V (p(V) <- G)` or `p <- G`
                // where q has a positive nonnegated occurrence in G
                for formula in theory {
                    match formula.unbox() {
                        UnboxedFormula::BinaryFormula {
                            connective: fol::BinaryConnective::ReverseImplication,
                            lhs: fol::Formula::AtomicFormula(head),
                            rhs,
                        } => {
                            if let fol::AtomicFormula::Atom(atom) = head {
                                let p = atom.predicate();
                                if intensional.contains(&p) {
                                    for q in intensional.iter() {
                                        if rhs.contains_positive_nonnegated_occurrence(q) {
                                            dependency_graph.update_edge(
                                                mapping[&p],
                                                mapping[q],
                                                (),
                                            );
                                        }
                                    }
                                }
                            }
                        }

                        UnboxedFormula::QuantifiedFormula {
                            quantification,
                            formula,
                        } => todo!(),

                        _ => (),
                    }
                }

                !is_cyclic_directed(&dependency_graph)
            }
            None => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use {super::Tightness, crate::syntax_tree::asp::mini_gringo::Program, std::str::FromStr};

    #[test]
    fn test_tightness() {
        for program in [
            "a.",
            "a :- not a.",
            "a :- not b. b :- not a.",
            "p(a) :- p.",
            "p(X) :- not q(X). q(X) :- p(X).",
        ] {
            let program = Program::from_str(program).unwrap();
            assert!(program.is_tight(program.predicates()))
        }

        for program in [
            "a :- a.",
            "a :- b. b :- a.",
            "p :- q, not r. p :- r. r :- p.",
        ] {
            let program = Program::from_str(program).unwrap();
            assert!(!program.is_tight(program.predicates()))
        }
    }
}
