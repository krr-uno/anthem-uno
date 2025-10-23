use {
    crate::{
        convenience::{
            apply::Apply,
            compose::Compose,
            unbox::{Unbox, fol::sigma_0::UnboxedFormula},
            visualizing::formula_trees::{
                FolNode, FolNodePrimitive, ancestors, grow_tree_from_formula, leafs, left_child,
            },
        },
        simplifying::fol::sigma_0::intuitionistic::{
            apply_negation_definition_inverse, apply_reverse_implication_definition,
        },
        syntax_tree::{
            GenericPredicate,
            asp::mini_gringo as asp,
            fol::sigma_0::{self as fol, Quantification, Quantifier},
        },
    },
    indexmap::IndexSet,
    petgraph::{
        algo::{has_path_connecting, is_cyclic_directed},
        graph::DiGraph,
    },
    std::collections::HashMap,
};

const TREE: &[fn(fol::Formula) -> fol::Formula] = &[
    apply_negation_definition_inverse,
    apply_reverse_implication_definition,
];

impl fol::Formula {
    fn contains_positive_nonnegated_occurrence(&self, predicate: &fol::Predicate) -> bool {
        let mut flag = false;

        // Convert every `F -> false` into `not F` and every `F <- G` into `G -> F`
        let mut tree_prep = [TREE].concat().into_iter().compose();
        let formula = self.clone().apply_fixpoint(&mut tree_prep);
        let (_, tree) = grow_tree_from_formula(formula);

        // Ensure the tree is a tree
        assert!(!is_cyclic_directed(&tree));

        // Every occurrence of a predicate occurs in a leaf node
        // Iterate through leaf nodes, check ancestors
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

                        // An occurrence of a predicate is negated if it has an ancestor in tree who is `not`
                        // Add 1 to the count for every `not` ancestor, every `<->` ancestor, and every `->` ancestor when occurrence is in left subtree
                        for a in ancestors(&tree, index) {
                            let ancestor = tree[a].clone();
                            match ancestor.primitive {
                                FolNodePrimitive::Implication => {
                                    // Ensure index occurs in lhs subtree (antecedent) of ancestor
                                    let lhs = left_child(&tree, a).unwrap();
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

                        if !negated && positive_count % 2 == 0 {
                            flag = true;
                        }
                    }
                }
            }
        }

        flag
    }
}

impl fol::Theory {
    pub(crate) fn predicate_dependency_graph(
        self,
        intensional_predicates: IndexSet<fol::Predicate>,
    ) -> Option<DiGraph<String, i32>> {
        match self.clark_normal_form(&intensional_predicates) {
            Some(cnf) => {
                let mut dependency_graph = DiGraph::<String, i32>::new();
                let mut mapping = HashMap::new();

                // Add intensional predicates as vertices
                for predicate in intensional_predicates.iter() {
                    let node = dependency_graph
                        .add_node(format!("{}/{}", predicate.symbol, predicate.arity));
                    mapping.insert(predicate.clone(), node);
                }

                // Add edge (p,q) if theory contains a formula `forall V (p(V) <- G)` or `p <- G`
                // where q has a positive nonnegated occurrence in G
                for formula in cnf {
                    match formula.unbox() {
                        UnboxedFormula::BinaryFormula {
                            connective: fol::BinaryConnective::ReverseImplication,
                            lhs: fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(atom)),
                            rhs,
                        } => {
                            let p = atom.predicate();
                            if intensional_predicates.contains(&p) {
                                for q in intensional_predicates.iter() {
                                    if rhs.contains_positive_nonnegated_occurrence(q) {
                                        dependency_graph.update_edge(mapping[&p], mapping[q], 1);
                                    }
                                }
                            }
                        }

                        UnboxedFormula::QuantifiedFormula {
                            quantification:
                                Quantification {
                                    quantifier: Quantifier::Forall,
                                    variables,
                                },
                            formula: inner,
                        } => {
                            if let UnboxedFormula::BinaryFormula {
                                connective: fol::BinaryConnective::ReverseImplication,
                                lhs: fol::Formula::AtomicFormula(head),
                                rhs,
                            } = inner.unbox()
                            {
                                let hvars = head.variables();
                                let variables: IndexSet<fol::Variable> =
                                    IndexSet::from_iter(variables);
                                if let fol::AtomicFormula::Atom(atom) = head {
                                    let p = atom.predicate();
                                    if intensional_predicates.contains(&p)
                                        && hvars.is_subset(&variables)
                                        && variables.is_subset(&hvars)
                                    {
                                        for q in intensional_predicates.iter() {
                                            if rhs.contains_positive_nonnegated_occurrence(q) {
                                                dependency_graph.update_edge(
                                                    mapping[&p],
                                                    mapping[q],
                                                    1,
                                                );
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        _ => (),
                    }
                }
                Some(dependency_graph)
            }

            None => {
                println!("theory cannot be converted to Clark Normal Form");
                None
            }
        }
    }
}

pub trait Tightness {
    fn is_tight(&self, intensional_predicates: IndexSet<GenericPredicate>) -> bool;
}

impl Tightness for asp::Program {
    fn is_tight(&self, intensional_predicates: IndexSet<GenericPredicate>) -> bool {
        // TODO: is this check necessary?
        let program_predicates: IndexSet<GenericPredicate> =
            self.predicates().into_iter().map(|p| p.into()).collect();
        assert!(
            program_predicates.is_subset(&intensional_predicates)
                && program_predicates.is_superset(&intensional_predicates)
        );

        let mut dependency_graph = DiGraph::<(), ()>::new();
        let mut mapping = HashMap::new();

        for predicate in intensional_predicates.into_iter().map(asp::Predicate::from) {
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
    // This definition of tightness is defined for completable theories
    // (or any theory that can be converted to Clark Normal Form)
    fn is_tight(&self, intensional_predicates: IndexSet<GenericPredicate>) -> bool {
        let intensional = IndexSet::from_iter(intensional_predicates.into_iter().map(|p| p.into()));
        match self.clone().predicate_dependency_graph(intensional) {
            Some(graph) => !is_cyclic_directed(&graph),
            None => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use {
        super::Tightness,
        crate::syntax_tree::{asp::mini_gringo::Program, fol::sigma_0::Theory},
        indexmap::IndexSet,
        std::str::FromStr,
    };

    #[test]
    fn test_program_tightness() {
        for program in [
            "a.",
            "a :- not a.",
            "a :- not b. b :- not a.",
            "p(a) :- p.",
            "p(X) :- not q(X). q(X) :- p(X).",
        ] {
            let program = Program::from_str(program).unwrap();
            let intensional =
                IndexSet::from_iter(program.predicates().into_iter().map(|p| p.into()));
            assert!(program.is_tight(intensional))
        }

        for program in [
            "a :- a.",
            "a :- b. b :- a.",
            "p :- q, not r. p :- r. r :- p.",
        ] {
            let program = Program::from_str(program).unwrap();
            let intensional =
                IndexSet::from_iter(program.predicates().into_iter().map(|p| p.into()));
            assert!(!program.is_tight(intensional))
        }
    }

    #[test]
    fn test_theory_tightness() {
        for theory in [
            "p <- q.",
            "p <- ( (p -> q) and (p -> r) ).",
            "forall X Y ( ((X = a and Y = a) or (X = a and Y = b)) -> p(X,Y) ). forall X (exists Y p(X,Y) -> q(X)).",
            "forall X ( #false -> p(X) ). forall X ( not p(X) -> q(X) ).",
            "forall X ( q(X) and not not p(X) -> p(X) ).",
            "forall X ( (not not ( (p(X) -> q(X)) -> r(X)) ) -> p(X)).",
        ] {
            let theory = Theory::from_str(theory).unwrap();
            let intensionals = theory.predicates().into_iter().map(|p| p.into()).collect();
            assert!(theory.is_tight(intensionals))
        }

        for theory in [
            "p <- p.",
            "p <- (r -> q). q <- p.",
            "forall X Y ( p(X,Y) or exists Z (t(X,Z) and t(Z,Y)) -> t(X,Y) ).",
            "forall X ( ((p(X) -> q(X)) -> r(X)) -> p(X)).",
        ] {
            let theory = Theory::from_str(theory).unwrap();
            let intensionals = theory.predicates().into_iter().map(|p| p.into()).collect();
            assert!(!theory.is_tight(intensionals))
        }
    }
}
