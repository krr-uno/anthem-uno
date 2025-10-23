use {
    super::tau_star::TauStar,
    crate::{
        convenience::{apply::Apply, compose::Compose, variable_selection::VariableSelection},
        simplifying::fol::sigma_0::intuitionistic::{
            remove_annihilations, remove_empty_quantifications, remove_idempotences,
            remove_identities, remove_orphaned_variables,
        },
        syntax_tree::{
            asp::mini_gringo_cl::{self as asp, BodyLiteral, ConditionalHead},
            fol::sigma_0::{
                Atom, AtomicFormula, BinaryConnective, Comparison, Formula, GeneralTerm, Guard,
                Quantification, Quantifier, Relation, Sort, Theory, UnaryConnective, Variable,
            },
        },
    },
    indexmap::IndexSet,
};

pub const PREPROCESS: &[fn(Formula) -> Formula] = &[
    remove_identities,
    remove_annihilations,
    remove_idempotences,
    remove_orphaned_variables,
    remove_empty_quantifications,
];

/// Choose fresh variants of `Vn` by incrementing `n`
fn choose_fresh_global_variables(program: &asp::Program) -> Vec<String> {
    let mut max_arity = 0;
    for rule in program.rules.iter() {
        let head_arity = rule.head.arity();
        if head_arity > max_arity {
            max_arity = head_arity;
        }
    }
    program.choose_fresh_variables("V", max_arity)
}

// // |t|
// // exists I$ (Z = I$ & val_t(I$))
// fn construct_absolute_value_formula(
//     valti: Formula,
//     i_var: fol::Variable,
//     z: fol::Variable,
// ) -> Formula {
//     let z_var_term = variable_to_general_term(z);

//     // Z = |I|
//     let zequals = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
//         term: z_var_term,
//         guards: vec![fol::Guard {
//             relation: fol::Relation::Equal,
//             term: GeneralTerm::IntegerTerm(fol::IntegerTerm::UnaryOperation {
//                 op: fol::UnaryOperator::AbsoluteValue,
//                 arg: fol::IntegerTerm::Variable(i_var.name.clone()).into(),
//             }),
//         }],
//     }));

//     Formula::QuantifiedFormula {
//         quantification: fol::Quantification {
//             quantifier: fol::Quantifier::Exists,
//             variables: vec![i_var],
//         },
//         formula: Formula::BinaryFormula {
//             connective: fol::BinaryConnective::Conjunction,
//             lhs: zequals.into(),
//             rhs: valti.into(),
//         }
//         .into(),
//     }
// }

// // Translate a first-order body literal
// fn tau_b_first_order_literal(
//     l: asp::Literal,
//     taken_vars: &mut IndexSet<fol::Variable>,
// ) -> Formula {
//     let atom = l.atom;
//     let terms = atom.terms;
//     let arity = terms.len();
//     let varnames = choose_fresh_variable_names(taken_vars, "Z", arity);

//     // Compute val_t1(Z1) & val_t2(Z2) & ... & val_tk(Zk)
//     let mut var_terms: Vec<GeneralTerm> = Vec::with_capacity(arity);
//     let mut var_vars: Vec<fol::Variable> = Vec::with_capacity(arity);
//     let mut valtz_vec: Vec<Formula> = Vec::with_capacity(arity);
//     for (i, t) in terms.iter().enumerate() {
//         let var = fol::Variable {
//             sort: fol::Sort::General,
//             name: varnames[i].clone(),
//         };
//         var_terms.push(GeneralTerm::Variable(varnames[i].clone()));
//         var_vars.push(var.clone());
//         valtz_vec.push(val_agc::val(t.clone(), var, taken_vars.clone()));
//     }
//     let valtz = Formula::conjoin(valtz_vec);

//     // Compute p(Z1, Z2, ..., Zk)
//     let p_zk = Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
//         predicate_symbol: atom.predicate_symbol,
//         terms: var_terms,
//     }));

//     // Compute tau^b(B)
//     match l.sign {
//         asp::Sign::NoSign => Formula::QuantifiedFormula {
//             quantification: fol::Quantification {
//                 quantifier: fol::Quantifier::Exists,
//                 variables: var_vars,
//             },
//             formula: Formula::BinaryFormula {
//                 connective: fol::BinaryConnective::Conjunction,
//                 lhs: valtz.into(),
//                 rhs: p_zk.into(),
//             }
//             .into(),
//         },
//         asp::Sign::Negation => Formula::QuantifiedFormula {
//             quantification: fol::Quantification {
//                 quantifier: fol::Quantifier::Exists,
//                 variables: var_vars,
//             },
//             formula: Formula::BinaryFormula {
//                 connective: fol::BinaryConnective::Conjunction,
//                 lhs: valtz.into(),
//                 rhs: Formula::UnaryFormula {
//                     connective: fol::UnaryConnective::Negation,
//                     formula: p_zk.into(),
//                 }
//                 .into(),
//             }
//             .into(),
//         },
//         asp::Sign::DoubleNegation => Formula::QuantifiedFormula {
//             quantification: fol::Quantification {
//                 quantifier: fol::Quantifier::Exists,
//                 variables: var_vars,
//             },
//             formula: Formula::BinaryFormula {
//                 connective: fol::BinaryConnective::Conjunction,
//                 lhs: valtz.into(),
//                 rhs: Formula::UnaryFormula {
//                     connective: fol::UnaryConnective::Negation,
//                     formula: Formula::UnaryFormula {
//                         connective: fol::UnaryConnective::Negation,
//                         formula: p_zk.into(),
//                     }
//                     .into(),
//                 }
//                 .into(),
//             }
//             .into(),
//         },
//     }
// }

// Translate a propositional body literal
// fn tau_b_propositional_literal(l: asp::Literal) -> Formula {
//     let atom = l.atom;
//     match l.sign {
//         asp::Sign::NoSign => Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
//             predicate_symbol: atom.predicate_symbol,

//             terms: vec![],
//         })),
//         asp::Sign::Negation => Formula::UnaryFormula {
//             connective: fol::UnaryConnective::Negation,
//             formula: Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
//                 predicate_symbol: atom.predicate_symbol,
//                 terms: vec![],
//             }))
//             .into(),
//         },
//         asp::Sign::DoubleNegation => Formula::UnaryFormula {
//             connective: fol::UnaryConnective::Negation,
//             formula: Formula::UnaryFormula {
//                 connective: fol::UnaryConnective::Negation,
//                 formula: Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
//                     predicate_symbol: atom.predicate_symbol,
//                     terms: vec![],
//                 }))
//                 .into(),
//             }
//             .into(),
//         },
//     }
// }

// val_t(Z)
pub(crate) fn val(t: asp::Term, z: Variable, taken_variables: IndexSet<Variable>) -> Formula {
    todo!()
}

// val_t1(Z1) & val_t2(Z2) & ... & val_tn(Zn)
fn valtz(mut terms: Vec<asp::Term>, mut variables: Vec<Variable>) -> Formula {
    Formula::conjoin(
        terms
            .drain(..)
            .zip(variables.drain(..))
            .map(|(t, v)| val(t, v)),
    )
}

// Translate a body literal
fn tau_b_literal(l: asp::Literal, taken_vars: IndexSet<Variable>) -> Formula {
    let atom = l.atom;
    let terms = atom.terms;
    let arity = terms.len();
    let varnames = taken_vars.choose_fresh_variables("Z", arity);

    // val_t1(Z1) & val_t2(Z2) & ... & val_tk(Zk)
    let vars: Vec<Variable> = varnames
        .iter()
        .map(|s| Variable {
            name: s.to_string(),
            sort: Sort::General,
        })
        .collect();
    let val_t_z = valtz(terms, vars.clone());

    // Compute p(Z1, Z2, ..., Zk)
    let var_terms: Vec<GeneralTerm> = vars.iter().cloned().map(GeneralTerm::from).collect();
    let p_zk = Formula::AtomicFormula(AtomicFormula::Atom(Atom {
        predicate_symbol: atom.predicate_symbol,
        terms: var_terms,
    }));

    // Compute tau^b(B)
    let inner = match l.sign {
        asp::Sign::NoSign => Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: val_t_z.into(),
            rhs: p_zk.into(),
        },

        asp::Sign::Negation => Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: val_t_z.into(),
            rhs: Formula::UnaryFormula {
                connective: UnaryConnective::Negation,
                formula: p_zk.into(),
            }
            .into(),
        },

        asp::Sign::DoubleNegation => Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: val_t_z.into(),
            rhs: Formula::UnaryFormula {
                connective: UnaryConnective::Negation,
                formula: Formula::UnaryFormula {
                    connective: UnaryConnective::Negation,
                    formula: p_zk.into(),
                }
                .into(),
            }
            .into(),
        },
    };

    if arity > 0 {
        Formula::QuantifiedFormula {
            quantification: Quantification {
                quantifier: Quantifier::Exists,
                variables: vars,
            },
            formula: inner.into(),
        }
    } else {
        let mut prep = [PREPROCESS].concat().into_iter().compose();
        inner.apply_fixpoint(&mut prep)
    }
}

// Translate a body comparison
fn tau_b_comparison(c: asp::Comparison, taken_vars: IndexSet<Variable>) -> Formula {
    let varnames = taken_vars.choose_fresh_variables("Z", 2);

    // Compute val_t1(Z1) & val_t2(Z2)
    let term_z1 = GeneralTerm::Variable(varnames[0].clone());
    let term_z2 = GeneralTerm::Variable(varnames[1].clone());
    let var_z1 = Variable {
        sort: Sort::General,
        name: varnames[0].clone(),
    };
    let var_z2 = Variable {
        sort: Sort::General,
        name: varnames[1].clone(),
    };

    let valtz = Formula::BinaryFormula {
        connective: BinaryConnective::Conjunction,
        lhs: val(c.lhs, var_z1.clone(), taken_vars.clone()).into(),
        rhs: val(c.rhs, var_z2.clone(), taken_vars).into(),
    };

    Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Exists,
            variables: vec![var_z1, var_z2],
        },
        formula: Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: valtz.into(),
            rhs: Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
                term: term_z1,
                guards: vec![Guard {
                    relation: Relation::from(c.relation),
                    term: term_z2,
                }],
            }))
            .into(),
        }
        .into(),
    }
}

// Translate a body literal or comparison
fn tau_b(f: asp::AtomicFormula) -> Formula {
    let mut taken_vars = IndexSet::new();
    for var in f.variables().iter() {
        taken_vars.insert(Variable {
            name: var.to_string(),
            sort: Sort::General,
        });
    }
    match f {
        asp::AtomicFormula::Literal(l) => tau_b_literal(l, taken_vars),
        asp::AtomicFormula::Comparison(c) => tau_b_comparison(c, taken_vars),
    }
}

// Translate a conditional literal l of the first kind with global variables z
fn tau_b_cl(l: asp::ConditionalLiteral, z: &IndexSet<asp::Variable>) -> Formula {
    let head = l.head.clone();
    let conditions = l.conditions.formulas.clone();

    // A variable is global in H : L if it occurs in H but not L
    let body_vars = l.conditions.variables();
    let mut global_cl_vars = head.variables();
    global_cl_vars.retain(|v| !body_vars.contains(v));

    let mut local_vars = l.variables();
    local_vars.retain(|v| !(z.contains(v) || global_cl_vars.contains(v)));

    let consequent = match head {
        ConditionalHead::AtomicFormula(a) => tau_b(a.clone()),
        ConditionalHead::Falsity => Formula::AtomicFormula(AtomicFormula::Falsity),
    };

    let mut formulas = vec![];
    for c in conditions.iter() {
        formulas.push(tau_b(c.clone()));
    }
    let antecedent = Formula::conjoin(formulas);

    let inner_formula = match antecedent {
        Formula::AtomicFormula(AtomicFormula::Truth) => consequent,
        _ => Formula::BinaryFormula {
            connective: BinaryConnective::Implication,
            lhs: antecedent.into(),
            rhs: consequent.into(),
        },
    };

    if local_vars.is_empty() {
        inner_formula
    } else {
        let mut variables = vec![];
        for v in local_vars.iter() {
            variables.push(Variable {
                name: v.0.clone(),
                sort: Sort::General,
            });
        }
        Formula::QuantifiedFormula {
            quantification: Quantification {
                quantifier: Quantifier::Forall,
                variables,
            },
            formula: inner_formula.into(),
        }
    }
}

// Translate a rule body
fn tau_body(b: asp::Body, z: IndexSet<asp::Variable>) -> Formula {
    let mut formulas = Vec::new();
    for f in b.formulas.iter() {
        match f {
            BodyLiteral::ConditionalLiteral(cl) => formulas.push(tau_b_cl(cl.clone(), &z)),
        }
    }
    Formula::conjoin(formulas)
}

// Translate a rule using a pre-defined list of global variables
fn tau_star_rule(r: asp::Rule, globals: &[String]) -> Formula {
    let mut prep = [PREPROCESS].concat().into_iter().compose();

    let body = tau_body(r.body.clone(), r.global_variables());

    match r.head.predicate() {
        Some(predicate) => {
            // V1, ..., Vk
            let kvars = if predicate.arity > 0 {
                globals[0..predicate.arity]
                    .into_iter()
                    .map(|s| Variable {
                        name: s.to_string(),
                        sort: Sort::General,
                    })
                    .collect()
            } else {
                Vec::new()
            };

            // val_t1(V1) & ... & val_tk(Vk)
            let val_t_v = match r.head.terms() {
                Some(terms) => valtz(terms.to_vec(), kvars.clone()),
                None => Formula::AtomicFormula(AtomicFormula::Truth),
            };

            let consequent = if predicate.arity > 0 {
                // Atom with variables in the head
                Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: predicate.symbol,
                    terms: kvars
                        .iter()
                        .map(|v| GeneralTerm::Variable(v.name.clone()))
                        .collect(),
                }))
            } else {
                // Propositional atom in the head
                Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: predicate.symbol,
                    terms: vec![],
                }))
            };

            let antecedent = if r.is_choice_rule() {
                // Choice rule
                // not not p(V)
                let dbl_neg_head = Formula::UnaryFormula {
                    connective: UnaryConnective::Negation,
                    formula: Formula::UnaryFormula {
                        connective: UnaryConnective::Negation,
                        formula: consequent.clone().into(),
                    }
                    .into(),
                };

                Formula::BinaryFormula {
                    connective: BinaryConnective::Conjunction,
                    lhs: Formula::BinaryFormula {
                        connective: BinaryConnective::Conjunction,
                        lhs: val_t_v.into(),
                        rhs: body.into(),
                    }
                    .into(),
                    rhs: dbl_neg_head.into(),
                }
            } else {
                // Basic rule
                Formula::BinaryFormula {
                    connective: BinaryConnective::Conjunction,
                    lhs: val_t_v.into(),
                    rhs: body.into(),
                }
            };

            Formula::BinaryFormula {
                connective: BinaryConnective::Implication,
                lhs: antecedent.into(),
                rhs: consequent.into(),
            }
        }
        // Handles the case when we have a rule with an empty head
        None => Formula::BinaryFormula {
            connective: BinaryConnective::Implication,
            lhs: body.into(),
            rhs: Formula::AtomicFormula(AtomicFormula::Falsity).into(),
        },
    }
    .universal_closure()
    .apply_fixpoint(&mut prep)
}

fn tau_star(p: asp::Program) -> Theory {
    let globals = choose_fresh_global_variables(&p);
    let mut formulas: Vec<Formula> = vec![]; // { forall G V ( val_t(V) & tau^B(Body) -> p(V) ), ... }
    for r in p.rules {
        formulas.push(tau_star_rule(r, &globals));
    }
    Theory { formulas }
}

impl TauStar for asp::Program {
    type Output = Theory;

    fn tau_star(self) -> Self::Output {
        tau_star(self)
    }
}
