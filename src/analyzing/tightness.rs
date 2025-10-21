use {
    crate::{
        convenience::unbox::{Unbox, fol::sigma_0::UnboxedFormula},
        syntax_tree::{asp::mini_gringo as asp, fol::sigma_0 as fol},
    },
    indexmap::IndexSet,
    petgraph::{
        algo::is_cyclic_directed,
        graph::{DiGraph, NodeIndex},
        visit::EdgeRef,
    },
    std::collections::{HashMap, HashSet},
};

#[derive(Clone, Copy, Eq, PartialEq, Hash)]
enum FolNodePrimitive {
    Forall,
    Exists,
    Conjunction,
    Disjunction,
    Implication,
    Equivalence,
    Negation,
    Atomic,
}

#[derive(Clone, Eq, PartialEq, Hash)]
struct FolNode {
    primitive: FolNodePrimitive,
    content: String,
}

// Return a tree rooted at the node corresponding to top-level connective in formula (index)
fn grow_tree_from_formula(formula: fol::Formula) -> (NodeIndex, DiGraph<FolNode, ()>) {
    // Create new subtree
    let mut tree = DiGraph::<FolNode, ()>::new();

    let index = match formula.unbox() {
        UnboxedFormula::AtomicFormula(atomic_formula) => {
            let node = tree.add_node(FolNode {
                primitive: FolNodePrimitive::Atomic,
                content: format!("{atomic_formula}"),
            });
            node
        }

        UnboxedFormula::UnaryFormula {
            connective,
            formula,
        } => match connective {
            fol::UnaryConnective::Negation => {
                let (subtree_root_index, subtree) = grow_tree_from_formula(formula);

                // Add subtree nodes to tree, mapping subtree indices to tree indices
                let mut mapping = HashMap::new();
                for subtree_index in subtree.node_indices() {
                    let tree_index = tree.add_node(subtree[subtree_index].clone());
                    mapping.insert(subtree_index, tree_index);
                }

                // Add subtree edges to tree
                for node in subtree.node_indices() {
                    // Iterate over outgoing edges
                    for edge in subtree.edges(node) {
                        tree.update_edge(mapping[&node], mapping[&edge.target()], ());
                    }
                }

                // Root the new tree at node
                let node = tree.add_node(FolNode {
                    primitive: FolNodePrimitive::Negation,
                    content: format!("not"),
                });
                tree.update_edge(node, mapping[&subtree_root_index], ());
                node
            }
        },

        UnboxedFormula::BinaryFormula {
            connective,
            lhs,
            rhs,
        } => {
            let (primitive, content) = match connective {
                fol::BinaryConnective::Conjunction => {
                    (FolNodePrimitive::Conjunction, format!("and"))
                }
                fol::BinaryConnective::Disjunction => {
                    (FolNodePrimitive::Disjunction, format!("or"))
                }
                fol::BinaryConnective::Implication => {
                    (FolNodePrimitive::Implication, format!("implies"))
                }
                fol::BinaryConnective::Equivalence => {
                    (FolNodePrimitive::Equivalence, format!("equivalent"))
                }
                fol::BinaryConnective::ReverseImplication => unreachable!(),
            };

            let (lhs_root_index, lhs_subtree) = grow_tree_from_formula(lhs);
            let (rhs_root_index, rhs_subtree) = grow_tree_from_formula(rhs);

            // Add subtree nodes to tree, mapping subtree indices to tree indices
            let mut lhs_mapping = HashMap::new();
            let mut rhs_mapping = HashMap::new();

            for subtree_index in lhs_subtree.node_indices() {
                let tree_index = tree.add_node(lhs_subtree[subtree_index].clone());
                lhs_mapping.insert(subtree_index, tree_index);
            }

            for subtree_index in rhs_subtree.node_indices() {
                let tree_index = tree.add_node(rhs_subtree[subtree_index].clone());
                rhs_mapping.insert(subtree_index, tree_index);
            }

            // Add subtree edges to tree
            for node in lhs_subtree.node_indices() {
                for edge in lhs_subtree.edges(node) {
                    tree.update_edge(lhs_mapping[&node], lhs_mapping[&edge.target()], ());
                }
            }

            for node in rhs_subtree.node_indices() {
                for edge in rhs_subtree.edges(node) {
                    tree.update_edge(rhs_mapping[&node], rhs_mapping[&edge.target()], ());
                }
            }

            // Root the new tree at node (with two children, lhs_subtree and rhs_subtree)
            let node = tree.add_node(FolNode { primitive, content });
            tree.update_edge(node, lhs_mapping[&lhs_root_index], ());
            tree.update_edge(node, rhs_mapping[&rhs_root_index], ());

            node
        }

        UnboxedFormula::QuantifiedFormula {
            quantification,
            formula,
        } => {
            let (primitive, content) = match quantification.quantifier {
                fol::Quantifier::Forall => (FolNodePrimitive::Forall, format!("{quantification}")),
                fol::Quantifier::Exists => (FolNodePrimitive::Exists, format!("{quantification}")),
            };

            let (subtree_root_index, subtree) = grow_tree_from_formula(formula);

            // Add subtree nodes to tree, mapping subtree indices to tree indices
            let mut mapping = HashMap::new();
            for subtree_index in subtree.node_indices() {
                let tree_index = tree.add_node(subtree[subtree_index].clone());
                mapping.insert(subtree_index, tree_index);
            }

            // Add subtree edges to tree
            for node in subtree.node_indices() {
                // Iterate over outgoing edges
                for edge in subtree.edges(node) {
                    tree.update_edge(mapping[&node], mapping[&edge.target()], ());
                }
            }

            // Root the new tree at node
            let node = tree.add_node(FolNode { primitive, content });
            tree.update_edge(node, mapping[&subtree_root_index], ());

            node
        }
    };

    (index, tree)
}

impl fol::Formula {
    fn contains_positive_nonnegated_occurrence(&self, predicate: &fol::Predicate) -> bool {
        // 1. Convert every `F -> false` into `not F` and every `F <- G` into `G -> F`
        // 2. An occurrence of a predicate is negated if it has an ancestor who is `not`
        // 3. Add 1 to the count for every `not` ancestor, every `<->` ancestor, and every `->` ancestor when occurrence is left child

        // every occurrence of a predicate occurs in a leaf node
        // iterate through leaf nodes, check ancestors
        todo!()
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
