use {
    super::tau_star::TauStar,
    crate::syntax_tree::{asp::mini_gringo_cl as asp, fol::sigma_0 as fol},
};

// // |t|
// // exists I$ (Z = I$ & val_t(I$))
// fn construct_absolute_value_formula(
//     valti: fol::Formula,
//     i_var: fol::Variable,
//     z: fol::Variable,
// ) -> fol::Formula {
//     let z_var_term = variable_to_general_term(z);

//     // Z = |I|
//     let zequals = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
//         term: z_var_term,
//         guards: vec![fol::Guard {
//             relation: fol::Relation::Equal,
//             term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::UnaryOperation {
//                 op: fol::UnaryOperator::AbsoluteValue,
//                 arg: fol::IntegerTerm::Variable(i_var.name.clone()).into(),
//             }),
//         }],
//     }));

//     fol::Formula::QuantifiedFormula {
//         quantification: fol::Quantification {
//             quantifier: fol::Quantifier::Exists,
//             variables: vec![i_var],
//         },
//         formula: fol::Formula::BinaryFormula {
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
// ) -> fol::Formula {
//     let atom = l.atom;
//     let terms = atom.terms;
//     let arity = terms.len();
//     let varnames = choose_fresh_variable_names(taken_vars, "Z", arity);

//     // Compute val_t1(Z1) & val_t2(Z2) & ... & val_tk(Zk)
//     let mut var_terms: Vec<fol::GeneralTerm> = Vec::with_capacity(arity);
//     let mut var_vars: Vec<fol::Variable> = Vec::with_capacity(arity);
//     let mut valtz_vec: Vec<fol::Formula> = Vec::with_capacity(arity);
//     for (i, t) in terms.iter().enumerate() {
//         let var = fol::Variable {
//             sort: fol::Sort::General,
//             name: varnames[i].clone(),
//         };
//         var_terms.push(fol::GeneralTerm::Variable(varnames[i].clone()));
//         var_vars.push(var.clone());
//         valtz_vec.push(val_agc::val(t.clone(), var, taken_vars.clone()));
//     }
//     let valtz = fol::Formula::conjoin(valtz_vec);

//     // Compute p(Z1, Z2, ..., Zk)
//     let p_zk = fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
//         predicate_symbol: atom.predicate_symbol,
//         terms: var_terms,
//     }));

//     // Compute tau^b(B)
//     match l.sign {
//         asp::Sign::NoSign => fol::Formula::QuantifiedFormula {
//             quantification: fol::Quantification {
//                 quantifier: fol::Quantifier::Exists,
//                 variables: var_vars,
//             },
//             formula: fol::Formula::BinaryFormula {
//                 connective: fol::BinaryConnective::Conjunction,
//                 lhs: valtz.into(),
//                 rhs: p_zk.into(),
//             }
//             .into(),
//         },
//         asp::Sign::Negation => fol::Formula::QuantifiedFormula {
//             quantification: fol::Quantification {
//                 quantifier: fol::Quantifier::Exists,
//                 variables: var_vars,
//             },
//             formula: fol::Formula::BinaryFormula {
//                 connective: fol::BinaryConnective::Conjunction,
//                 lhs: valtz.into(),
//                 rhs: fol::Formula::UnaryFormula {
//                     connective: fol::UnaryConnective::Negation,
//                     formula: p_zk.into(),
//                 }
//                 .into(),
//             }
//             .into(),
//         },
//         asp::Sign::DoubleNegation => fol::Formula::QuantifiedFormula {
//             quantification: fol::Quantification {
//                 quantifier: fol::Quantifier::Exists,
//                 variables: var_vars,
//             },
//             formula: fol::Formula::BinaryFormula {
//                 connective: fol::BinaryConnective::Conjunction,
//                 lhs: valtz.into(),
//                 rhs: fol::Formula::UnaryFormula {
//                     connective: fol::UnaryConnective::Negation,
//                     formula: fol::Formula::UnaryFormula {
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
// fn tau_b_propositional_literal(l: asp::Literal) -> fol::Formula {
//     let atom = l.atom;
//     match l.sign {
//         asp::Sign::NoSign => fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
//             predicate_symbol: atom.predicate_symbol,

//             terms: vec![],
//         })),
//         asp::Sign::Negation => fol::Formula::UnaryFormula {
//             connective: fol::UnaryConnective::Negation,
//             formula: fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
//                 predicate_symbol: atom.predicate_symbol,
//                 terms: vec![],
//             }))
//             .into(),
//         },
//         asp::Sign::DoubleNegation => fol::Formula::UnaryFormula {
//             connective: fol::UnaryConnective::Negation,
//             formula: fol::Formula::UnaryFormula {
//                 connective: fol::UnaryConnective::Negation,
//                 formula: fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
//                     predicate_symbol: atom.predicate_symbol,
//                     terms: vec![],
//                 }))
//                 .into(),
//             }
//             .into(),
//         },
//     }
// }

// Translate a rule using a pre-defined list of global variables
// fn tau_star_rule(r: &asp::Rule, globals: &[String]) -> fol::Formula {
// match r.head.predicate() {
//     Some(_) => {
//         todo!()
//     }
//     // Handles the case when we have a rule with an empty head
//     None => fol::Formula::BinaryFormula {
//         connective: fol::BinaryConnective::Implication,
//         lhs: tau_body(r.body.clone(), r.global_variables()).into(),
//         rhs: fol::Formula::AtomicFormula(fol::AtomicFormula::Falsity).into(),
//     }
//     .universal_closure(),
// }
// todo!()
//}

// fn tau_star(p: asp::Program) -> fol::Theory {
//     // let globals = choose_fresh_global_variables(&p);
//     // let mut formulas: Vec<fol::Formula> = vec![]; // { forall G V ( val_t(V) & tau^B(Body) -> p(V) ), ... }
//     // for r in p.rules.iter() {
//     //     formulas.push(tau_star_rule(r, &globals));
//     // }
//     // fol::Theory { formulas }
//     todo!()
// }

impl TauStar for asp::Program {
    type Output = fol::Theory;

    fn tau_star(self) -> Self::Output {
        //tau_star(self)
        todo!()
    }
}
