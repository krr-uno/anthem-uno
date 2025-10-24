use {
    super::tau_star::TauStar,
    crate::{
        convenience::{apply::Apply, compose::Compose, variable_selection::VariableSelection},
        simplifying::fol::sigma_0::intuitionistic::{
            remove_annihilations, remove_empty_quantifications, remove_idempotences,
            remove_identities, remove_orphaned_variables,
        },
        syntax_tree::{
            asp::mini_gringo_cl as asp,
            fol::sigma_0::{
                Atom, AtomicFormula, BinaryConnective, BinaryOperator, Comparison, Formula,
                GeneralTerm, Guard, IntegerTerm, Quantification, Quantifier, Relation, Sort,
                SymbolicTerm, Theory, UnaryConnective, UnaryOperator, Variable,
            },
        },
    },
    indexmap::{IndexMap, IndexSet},
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

fn choose_fresh_ijk(taken_variables: IndexSet<Variable>) -> IndexMap<String, Variable> {
    let mut fresh_int_vars = IndexMap::new();

    fresh_int_vars.insert(
        "I".to_string(),
        Variable {
            name: taken_variables.choose_fresh_variable("I"),
            sort: Sort::Integer,
        },
    );
    fresh_int_vars.insert(
        "J".to_string(),
        Variable {
            name: taken_variables.choose_fresh_variable("J"),
            sort: Sort::Integer,
        },
    );
    fresh_int_vars.insert(
        "K".to_string(),
        Variable {
            name: taken_variables.choose_fresh_variable("K"),
            sort: Sort::Integer,
        },
    );

    fresh_int_vars
}

// Z = t
fn construct_equality_formula(term: asp::Term, z: Variable) -> Formula {
    let rhs = match term {
        asp::Term::PrecomputedTerm(t) => match t {
            asp::PrecomputedTerm::Infimum => GeneralTerm::Infimum,
            asp::PrecomputedTerm::Supremum => GeneralTerm::Supremum,
            asp::PrecomputedTerm::Numeral(i) => GeneralTerm::IntegerTerm(IntegerTerm::Numeral(i)),
            asp::PrecomputedTerm::Symbol(s) => GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol(s)),
        },
        asp::Term::Variable(v) => GeneralTerm::Variable(v.0),
        _ => unreachable!(
            "equality should be between two variables or a variable and a precomputed term"
        ),
    };

    Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: z.into(),
        guards: vec![Guard {
            relation: Relation::Equal,
            term: rhs,
        }],
    }))
}

// op: +,-,*
// exists I J (Z = I op J & val_t1(I) & val_t2(J))
fn construct_total_function_formula(
    valti: Formula,
    valtj: Formula,
    binop: asp::BinaryOperator,
    i_var: Variable,
    j_var: Variable,
    z: Variable,
) -> Formula {
    // Z = I binop J
    let zequals = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: z.into(),
        guards: vec![Guard {
            relation: Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                op: match binop {
                    asp::BinaryOperator::Add => BinaryOperator::Add,
                    asp::BinaryOperator::Subtract => BinaryOperator::Subtract,
                    asp::BinaryOperator::Multiply => BinaryOperator::Multiply,
                    _ => unreachable!(
                        "addition, subtraction and multiplication are the only supported total functions"
                    ),
                },
                lhs: IntegerTerm::Variable(i_var.name.clone()).into(),
                rhs: IntegerTerm::Variable(j_var.name.clone()).into(),
            }),
        }],
    }));
    Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Exists,
            variables: vec![i_var, j_var],
        },
        formula: Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: Formula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                lhs: zequals.into(),
                rhs: valti.into(),
            }
            .into(),
            rhs: valtj.into(),
        }
        .into(),
    }
}

// t1..t2
// exists I J K (val_t1(I) & val_t2(J) & I <= K <= J & Z = K)
fn construct_interval_formula(
    valti: Formula,
    valtj: Formula,
    i_var: Variable,
    j_var: Variable,
    k_var: Variable,
    z: Variable,
) -> Formula {
    // I <= K <= J
    let range = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: GeneralTerm::IntegerTerm(IntegerTerm::Variable(i_var.name.clone())),
        guards: vec![
            Guard {
                relation: Relation::LessEqual,
                term: GeneralTerm::IntegerTerm(IntegerTerm::Variable(k_var.name.clone())),
            },
            Guard {
                relation: Relation::LessEqual,
                term: GeneralTerm::IntegerTerm(IntegerTerm::Variable(j_var.name.clone())),
            },
        ],
    }));

    // val_t1(I) & val_t2(J) & Z = k
    let subformula = Formula::BinaryFormula {
        connective: BinaryConnective::Conjunction,
        lhs: Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: valti.into(),
            rhs: valtj.into(),
        }
        .into(),
        rhs: Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
            term: z.into(),
            guards: vec![Guard {
                relation: Relation::Equal,
                term: GeneralTerm::IntegerTerm(IntegerTerm::Variable(k_var.name.clone())),
            }],
        }))
        .into(),
    };

    Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Exists,
            variables: vec![i_var, j_var, k_var],
        },
        formula: Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: subformula.into(),
            rhs: range.into(),
        }
        .into(),
    }
}

// |t|
// exists I$ (Z = I$ & val_t(I$))
fn construct_absolute_value_formula(valti: Formula, i_var: Variable, z: Variable) -> Formula {
    // Z = |I|
    let zequals = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: z.into(),
        guards: vec![Guard {
            relation: Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::UnaryOperation {
                op: UnaryOperator::AbsoluteValue,
                arg: IntegerTerm::Variable(i_var.name.clone()).into(),
            }),
        }],
    }));

    Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Exists,
            variables: vec![i_var],
        },
        formula: Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: zequals.into(),
            rhs: valti.into(),
        }
        .into(),
    }
}

// I,J,K must be integer variables
// f1: K * |J| <= |I| < (K+1) * |J|
fn division_helper_f1(i: Variable, j: Variable, k: Variable) -> Formula {
    // K * |J|
    let term1 = GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
        op: BinaryOperator::Multiply,
        lhs: IntegerTerm::Variable(k.name.clone()).into(),
        rhs: IntegerTerm::UnaryOperation {
            op: UnaryOperator::AbsoluteValue,
            arg: IntegerTerm::Variable(j.name.clone()).into(),
        }
        .into(),
    });

    // |I|
    let term2 = GeneralTerm::IntegerTerm(IntegerTerm::UnaryOperation {
        op: UnaryOperator::AbsoluteValue,
        arg: IntegerTerm::Variable(i.name.clone()).into(),
    });

    // (K+1) * |J|
    let term3 = GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
        op: BinaryOperator::Multiply,
        lhs: IntegerTerm::BinaryOperation {
            op: BinaryOperator::Add,
            lhs: IntegerTerm::Variable(k.name.clone()).into(),
            rhs: IntegerTerm::Numeral(1).into(),
        }
        .into(),
        rhs: IntegerTerm::UnaryOperation {
            op: UnaryOperator::AbsoluteValue,
            arg: IntegerTerm::Variable(j.name.clone()).into(),
        }
        .into(),
    });

    Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: term1,
        guards: vec![
            Guard {
                relation: Relation::LessEqual,
                term: term2,
            },
            Guard {
                relation: Relation::Less,
                term: term3,
            },
        ],
    }))
}

// f2: (I * J >= 0 & Z = K) v (I * J < 0 & Z = -K)
fn division_helper_f2(
    i: Variable, // Must be an integer variable
    j: Variable, // Must be an integer variable
    k: Variable, // Must be an integer variable
    z: Variable, // Must be a general variable
) -> Formula {
    // I * J
    let i_times_j = GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
        op: BinaryOperator::Multiply,
        lhs: IntegerTerm::Variable(i.name.clone()).into(),
        rhs: IntegerTerm::Variable(j.name.clone()).into(),
    });

    // I * J >= 0
    let ij_geq_zero = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: i_times_j.clone(),
        guards: vec![Guard {
            relation: Relation::GreaterEqual,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
        }],
    }));

    // Z = K
    let z_equals_k = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: z.clone().into(),
        guards: vec![Guard {
            relation: Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Variable(k.name.clone())),
        }],
    }));

    // I * J < 0
    let ij_less_zero = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: i_times_j,
        guards: vec![Guard {
            relation: Relation::Less,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
        }],
    }));

    // Z = -K
    let z_equals_neg_k = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: z.into(),
        guards: vec![Guard {
            relation: Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::UnaryOperation {
                op: UnaryOperator::Negative,
                arg: IntegerTerm::Variable(k.name).into(),
            }),
        }],
    }));

    Formula::BinaryFormula {
        connective: BinaryConnective::Disjunction,
        lhs: Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: ij_geq_zero.into(),
            rhs: z_equals_k.into(),
        }
        .into(),
        rhs: Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: ij_less_zero.into(),
            rhs: z_equals_neg_k.into(),
        }
        .into(),
    }
}

// Arguments must be integer variables
// f3: (I * J >= 0 & Z = I - K * J) v (I * J < 0 & Z = I + K * J)
fn division_helper_f3(i: Variable, j: Variable, k: Variable, z: Variable) -> Formula {
    // I * J
    let i_times_j = GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
        op: BinaryOperator::Multiply,
        lhs: IntegerTerm::Variable(i.name.clone()).into(),
        rhs: IntegerTerm::Variable(j.name.clone()).into(),
    });

    // I * J >= 0
    let ij_geq_zero = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: i_times_j.clone(),
        guards: vec![Guard {
            relation: Relation::GreaterEqual,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
        }],
    }));

    // I * J < 0
    let ij_less_zero = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: i_times_j,
        guards: vec![Guard {
            relation: Relation::Less,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
        }],
    }));

    // K * J
    let k_times_j = IntegerTerm::BinaryOperation {
        op: BinaryOperator::Multiply,
        lhs: IntegerTerm::Variable(k.name.clone()).into(),
        rhs: IntegerTerm::Variable(j.name.clone()).into(),
    };

    // Z = I - K * J
    let z_equals_i_minus = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: z.clone().into(),
        guards: vec![Guard {
            relation: Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                op: BinaryOperator::Subtract,
                lhs: IntegerTerm::Variable(i.name.clone()).into(),
                rhs: k_times_j.clone().into(),
            }),
        }],
    }));

    // Z = I + K * J
    let z_equals_i_plus = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: z.into(),
        guards: vec![Guard {
            relation: Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                op: BinaryOperator::Add,
                lhs: IntegerTerm::Variable(i.name.clone()).into(),
                rhs: k_times_j.into(),
            }),
        }],
    }));

    Formula::BinaryFormula {
        connective: BinaryConnective::Disjunction,
        lhs: Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: ij_geq_zero.into(),
            rhs: z_equals_i_minus.into(),
        }
        .into(),
        rhs: Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: ij_less_zero.into(),
            rhs: z_equals_i_plus.into(),
        }
        .into(),
    }
}

// Abstract Gringo compliant integer division and modulo.
// Follows Locally Tight Programs (2023), Conditional literals & Arithmetic (2025)
// Division: exists I J K (val_t1(I) & val_t2(J) & F1(IJK) & F2(IJKZ))
// Modulo:   exists I J K (val_t1(I) & val_t2(J) & F1(IJK) & F3(IJKZ))
fn construct_partial_function_formula(
    valti: Formula,
    valtj: Formula,
    binop: asp::BinaryOperator,
    i: Variable,
    j: Variable,
    k: Variable,
    z: Variable,
) -> Formula {
    assert_eq!(i.sort, Sort::Integer);
    assert_eq!(j.sort, Sort::Integer);
    assert_eq!(k.sort, Sort::Integer);
    assert_eq!(z.sort, Sort::General);

    let f1 = division_helper_f1(i.clone(), j.clone(), k.clone());

    let f = match binop {
        asp::BinaryOperator::Divide => division_helper_f2(i.clone(), j.clone(), k.clone(), z),
        asp::BinaryOperator::Modulo => division_helper_f3(i.clone(), j.clone(), k.clone(), z),
        _ => unreachable!("division and modulo are the only supported partial functions"),
    };

    Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Exists,
            variables: vec![i, j, k],
        },
        formula: Formula::conjoin([valti, valtj, f1, f]).into(),
    }
}

// val_t(Z)
fn val(t: asp::Term, z: Variable, taken_variables: IndexSet<Variable>) -> Formula {
    let mut taken_variables = taken_variables;
    taken_variables.insert(z.clone());
    for var in t.variables().iter() {
        taken_variables.insert(Variable {
            name: var.to_string(),
            sort: Sort::General,
        });
    }

    let fresh_int_vars = choose_fresh_ijk(taken_variables.clone());

    for (_, value) in fresh_int_vars.iter() {
        taken_variables.insert(value.clone());
    }

    match t {
        asp::Term::PrecomputedTerm(_) | asp::Term::Variable(_) => construct_equality_formula(t, z),
        asp::Term::UnaryOperation { op, arg } => match op {
            asp::UnaryOperator::Negative => {
                let lhs = asp::Term::PrecomputedTerm(asp::PrecomputedTerm::Numeral(0)); // Shorthand for 0 - t
                let valti = val(lhs, fresh_int_vars["I"].clone(), taken_variables.clone()); // val_t1(I)
                let valtj = val(*arg, fresh_int_vars["J"].clone(), taken_variables); // val_t2(J)
                construct_total_function_formula(
                    valti,
                    valtj,
                    asp::BinaryOperator::Subtract,
                    fresh_int_vars["I"].clone(),
                    fresh_int_vars["J"].clone(),
                    z,
                )
            }
            asp::UnaryOperator::AbsoluteValue => {
                let valti = val(*arg, fresh_int_vars["I"].clone(), taken_variables.clone()); // val_t1(I)
                construct_absolute_value_formula(valti, fresh_int_vars["I"].clone(), z)
            }
        },
        asp::Term::BinaryOperation { op, lhs, rhs } => {
            let valti = val(*lhs, fresh_int_vars["I"].clone(), taken_variables.clone()); // val_t1(I)
            let valtj = val(*rhs, fresh_int_vars["J"].clone(), taken_variables); // val_t2(J)
            match op {
                asp::BinaryOperator::Add
                | asp::BinaryOperator::Subtract
                | asp::BinaryOperator::Multiply => construct_total_function_formula(
                    valti,
                    valtj,
                    op,
                    fresh_int_vars["I"].clone(),
                    fresh_int_vars["J"].clone(),
                    z,
                ),
                asp::BinaryOperator::Divide | asp::BinaryOperator::Modulo => {
                    construct_partial_function_formula(
                        valti,
                        valtj,
                        op,
                        fresh_int_vars["I"].clone(),
                        fresh_int_vars["J"].clone(),
                        fresh_int_vars["K"].clone(),
                        z,
                    )
                }
                asp::BinaryOperator::Interval => construct_interval_formula(
                    valti,
                    valtj,
                    fresh_int_vars["I"].clone(),
                    fresh_int_vars["J"].clone(),
                    fresh_int_vars["K"].clone(),
                    z,
                ),
            }
        }
    }
}

// val_t1(Z1) & val_t2(Z2) & ... & val_tn(Zn)
fn valtz(mut terms: Vec<asp::Term>, mut variables: Vec<Variable>) -> Formula {
    Formula::conjoin(
        terms
            .drain(..)
            .zip(variables.drain(..))
            .map(|(t, v)| val(t, v, IndexSet::new())),
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

    // Compute tau^b(B) minus the existential quantifier
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
        asp::ConditionalHead::AtomicFormula(a) => tau_b(a.clone()),
        asp::ConditionalHead::Falsity => Formula::AtomicFormula(AtomicFormula::Falsity),
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
            asp::BodyLiteral::ConditionalLiteral(cl) => formulas.push(tau_b_cl(cl.clone(), &z)),
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
                    .iter()
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
