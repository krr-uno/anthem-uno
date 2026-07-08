use {
    crate::{
        convenience::variable_selection::VariableSelection,
        syntax_tree::asp::{gringo, mini_gringo_cl},
    },
    indexmap::IndexSet,
};

// Name anonymous variables
fn standardize_term(
    term: gringo::Term,
    taken_variables: &mut IndexSet<String>,
) -> mini_gringo_cl::Term {
    match term {
        gringo::Term::PrecomputedTerm(t) => mini_gringo_cl::Term::PrecomputedTerm(t.into()),
        gringo::Term::Variable(variable) => match variable.name {
            Some(name) => mini_gringo_cl::Term::Variable(mini_gringo_cl::Variable(name)),
            None => {
                let name = taken_variables.choose_fresh_variable("V");
                taken_variables.insert(name.clone());
                mini_gringo_cl::Term::Variable(mini_gringo_cl::Variable(name))
            }
        },
        gringo::Term::UnaryOperation { op, arg } => {
            let term = standardize_term(*arg, taken_variables);
            mini_gringo_cl::Term::UnaryOperation {
                op: op.into(),
                arg: term.into(),
            }
        }
        gringo::Term::BinaryOperation { op, lhs, rhs } => {
            let t1 = standardize_term(*lhs, taken_variables);
            let t2 = standardize_term(*rhs, taken_variables);
            mini_gringo_cl::Term::BinaryOperation {
                op: op.into(),
                lhs: t1.into(),
                rhs: t2.into(),
            }
        }
    }
}

fn standardize_atomic_formula(
    formula: gringo::AtomicFormula,
    taken_variables: &mut IndexSet<String>,
) -> mini_gringo_cl::AtomicFormula {
    match formula {
        gringo::AtomicFormula::Literal(literal) => {
            let std_terms = literal
                .atom
                .terms
                .into_iter()
                .map(|t| standardize_term(t, taken_variables))
                .collect();
            let inner = mini_gringo_cl::Literal {
                sign: literal.sign.into(),
                atom: mini_gringo_cl::Atom {
                    predicate_symbol: literal.atom.predicate_symbol,
                    terms: std_terms,
                },
            };
            mini_gringo_cl::AtomicFormula::Literal(inner)
        }
        gringo::AtomicFormula::Comparison(comparison) => {
            let lhs = standardize_term(comparison.lhs, taken_variables);
            let rhs = standardize_term(comparison.rhs, taken_variables);
            mini_gringo_cl::AtomicFormula::Comparison(mini_gringo_cl::Comparison {
                relation: comparison.relation.into(),
                lhs,
                rhs,
            })
        }
    }
}

fn standardize_conditional_literal(
    literal: gringo::ConditionalLiteral,
    taken_variables: &mut IndexSet<String>,
) -> mini_gringo_cl::ConditionalLiteral {
    let head = match literal.head {
        gringo::ConditionalHead::AtomicFormula(formula) => {
            let std_formula = standardize_atomic_formula(formula, taken_variables);
            mini_gringo_cl::ConditionalHead::AtomicFormula(std_formula)
        }
        gringo::ConditionalHead::Falsity => mini_gringo_cl::ConditionalHead::Falsity,
    };
    let formulas = literal
        .conditions
        .formulas
        .into_iter()
        .map(|f| standardize_atomic_formula(f, taken_variables))
        .collect();
    mini_gringo_cl::ConditionalLiteral {
        head,
        conditions: mini_gringo_cl::ConditionalBody { formulas },
    }
}

fn standardize_rule_head(
    head: gringo::Head,
    taken_variables: &mut IndexSet<String>,
) -> mini_gringo_cl::Head {
    let mut terms = Vec::new();

    if let Some(head_terms) = head.terms() {
        for term in head_terms {
            terms.push(standardize_term(term.clone(), taken_variables));
        }
    }

    match head {
        gringo::Head::Basic(atom) => mini_gringo_cl::Head::Basic(mini_gringo_cl::Atom {
            predicate_symbol: atom.predicate_symbol,
            terms,
        }),
        gringo::Head::Choice(atom) => mini_gringo_cl::Head::Choice(mini_gringo_cl::Atom {
            predicate_symbol: atom.predicate_symbol,
            terms,
        }),
        gringo::Head::Falsity => mini_gringo_cl::Head::Falsity,
    }
}

fn standardize_rule_body(
    body: gringo::Body,
    taken_variables: &mut IndexSet<String>,
) -> mini_gringo_cl::Body {
    let mut formulas = Vec::new();

    for literal in body.formulas {
        let formula = match literal {
            gringo::BodyLiteral::GfiveConditionalLiteral(cl) => {
                mini_gringo_cl::BodyLiteral::GfiveConditionalLiteral(
                    standardize_conditional_literal(cl, taken_variables),
                )
            }
            gringo::BodyLiteral::GsixConditionalLiteral(cl) => {
                mini_gringo_cl::BodyLiteral::GsixConditionalLiteral(
                    standardize_conditional_literal(cl, taken_variables),
                )
            }
        };
        formulas.push(formula);
    }

    mini_gringo_cl::Body { formulas }
}

pub fn standardize_rule(rule: gringo::Rule) -> mini_gringo_cl::Rule {
    let mut taken_variables = rule
        .named_variables()
        .into_iter()
        .map(|v| v.name.unwrap())
        .collect();

    let head = standardize_rule_head(rule.head, &mut taken_variables);
    let body = standardize_rule_body(rule.body, &mut taken_variables);

    mini_gringo_cl::Rule { head, body }
}

#[cfg(test)]
mod tests {
    use {
        super::{standardize_atomic_formula, standardize_rule, standardize_term},
        indexmap::IndexSet,
    };

    #[test]
    fn test_standardize_term() {
        for (src, target) in [
            ("_", "V"),
            ("(_+_)/_", "(V+V1)/V2"),
            ("_+1", "V+1"),
            ("_.._a", "V.._a"),
        ] {
            let src = standardize_term(src.parse().unwrap(), &mut IndexSet::new());
            let target = target.parse().unwrap();
            assert_eq!(src, target, "src != target: \n{src} != {target}")
        }
    }

    #[test]
    fn test_standardize_atomic_formula() {
        for (src, target) in [
            ("p(_+_, _)", "p(V+V1, V2)"),
            ("not pq(a, _, _ - 1)", "not pq(a, V, V1 - 1)"),
            ("not not choice(_)", "not not choice(V)"),
            ("_ = 5", "V = 5"),
            ("1..3 = 5 / _", "1..3 = 5 / V"),
        ] {
            let src = standardize_atomic_formula(src.parse().unwrap(), &mut IndexSet::new());
            let target = target.parse().unwrap();
            assert_eq!(src, target, "src != target: \n{src} != {target}")
        }
    }

    #[test]
    fn test_standardize_rule() {
        for (src, target) in [
            ("p(_) :- q(_).", "p(V) :- q(V1)."),
            ("{p(V)} :- q(_+1), t(V1).", "{p(V)} :- q(V2+1), t(V1)."),
            (":- _ < _, not p(V1).", ":- V < V2, not p(V1)."),
        ] {
            let src = standardize_rule(src.parse().unwrap());
            let target = target.parse().unwrap();
            assert_eq!(src, target, "src != target: \n{src} != {target}")
        }
    }
}
