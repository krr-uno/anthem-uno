use {
    crate::{
        convenience::unbox::{Unbox, fol::sigma_0::UnboxedFormula},
        syntax_tree::fol::sigma_0 as fol,
    },
    petgraph::{
        Direction::{Incoming, Outgoing},
        algo::is_cyclic_directed,
        dot::{Config, Dot},
        graph::{DiGraph, NodeIndex},
        visit::EdgeRef,
    },
    std::{collections::HashMap, fmt::Display, fs::File, io::Write},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(crate) enum FolNodePrimitive {
    Forall,
    Exists,
    Conjunction,
    Disjunction,
    Implication,
    Equivalence,
    Negation,
    Atomic,
}

#[derive(Clone, Eq, Debug, PartialEq, Hash)]
pub(crate) struct FolNode {
    pub primitive: FolNodePrimitive,
    pub content: String,
}

impl Display for FolNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, " {} ", self.content)
    }
}

type FormulaTree = DiGraph<FolNode, i32>;

// Return a tree rooted at the node corresponding to top-level connective in formula (index)
pub(crate) fn grow_tree_from_formula(formula: fol::Formula) -> (NodeIndex, FormulaTree) {
    // Create new subtree
    let mut tree = DiGraph::<FolNode, i32>::new();

    let index = match formula.unbox() {
        UnboxedFormula::AtomicFormula(atomic_formula) => tree.add_node(FolNode {
            primitive: FolNodePrimitive::Atomic,
            content: format!("{atomic_formula}"),
        }),

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
                        tree.update_edge(mapping[&node], mapping[&edge.target()], 0);
                    }
                }

                // Root the new tree at node
                let node = tree.add_node(FolNode {
                    primitive: FolNodePrimitive::Negation,
                    content: "not".to_string(),
                });
                tree.update_edge(node, mapping[&subtree_root_index], 0);
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
                    (FolNodePrimitive::Conjunction, "and".to_string())
                }
                fol::BinaryConnective::Disjunction => {
                    (FolNodePrimitive::Disjunction, "or".to_string())
                }
                fol::BinaryConnective::Implication => {
                    (FolNodePrimitive::Implication, "implies".to_string())
                }
                fol::BinaryConnective::Equivalence => {
                    (FolNodePrimitive::Equivalence, "equivalent".to_string())
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
                    tree.update_edge(lhs_mapping[&node], lhs_mapping[&edge.target()], 0);
                }
            }

            for node in rhs_subtree.node_indices() {
                for edge in rhs_subtree.edges(node) {
                    tree.update_edge(rhs_mapping[&node], rhs_mapping[&edge.target()], 0);
                }
            }

            // Root the new tree at node (with two children, lhs_subtree and rhs_subtree)
            let node = tree.add_node(FolNode { primitive, content });
            tree.update_edge(node, lhs_mapping[&lhs_root_index], 0);
            tree.update_edge(node, rhs_mapping[&rhs_root_index], 1);

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
                    tree.update_edge(mapping[&node], mapping[&edge.target()], 0);
                }
            }

            // Root the new tree at node
            let node = tree.add_node(FolNode { primitive, content });
            tree.update_edge(node, mapping[&subtree_root_index], 0);

            node
        }
    };

    (index, tree)
}

pub(crate) fn leafs(tree: &FormulaTree) -> Vec<NodeIndex> {
    let mut leafs = Vec::new();
    for index in tree.node_indices() {
        if tree.edges(index).count() == 0 {
            leafs.push(index);
        }
    }
    leafs
}

pub(crate) fn ancestors(tree: &FormulaTree, index: NodeIndex) -> Vec<NodeIndex> {
    // Ensure that tree is a tree
    assert!(!is_cyclic_directed(tree));

    let mut ancestors = Vec::new();

    let mut current = index;
    while let Some(edge) = tree.edges_directed(current, Incoming).next() {
        let parent = edge.source();
        ancestors.push(parent);
        current = parent;
    }

    ancestors
}

// Return first child with weight=0 on the connecting edge
// (rhs subtrees were linked with weight=1 during tree construction)
pub(crate) fn left_child(tree: &FormulaTree, index: NodeIndex) -> Option<NodeIndex> {
    let mut node = None;
    let children = tree.edges_directed(index, Outgoing);
    for child in children {
        if *child.weight() == 0 {
            node = Some(child.target());
            break;
        }
    }
    node
}
