use {
    crate::syntax_tree::{asp::mini_gringo as asp, fol::sigma_0 as fol},
    indexmap::IndexSet,
    petgraph::{algo::is_cyclic_directed, graph::DiGraph},
    std::collections::HashMap,
};

pub trait Tightness {
    fn is_tight(&self, intensional_predicates: IndexSet<asp::Predicate>) -> bool;
}

impl Tightness for asp::Program {
    fn is_tight(&self, intensional_predicates: IndexSet<asp::Predicate>) -> bool {

        // TODO: is this check necessary?
        if !(self.predicates().is_subset(&intensional_predicates) && self.predicates().is_superset(&intensional_predicates)) {
            return false
        }

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
        let intensional = IndexSet::from_iter(intensional_predicates.iter().map(|p| p.clone().into()));
        match self.clone().clark_normal_form(intensional) {
            Some(theory) => {
                todo!()
            },
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
