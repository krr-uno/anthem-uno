use {
    super::tau_star::TauStar,
    crate::{
        convenience::{apply::Apply, compose::Compose, variable_selection::VariableSelection},
        simplifying::fol::sigma_0::intuitionistic::{
            remove_conjunctive_identities, remove_empty_quantifications, remove_orphaned_variables,
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
    remove_conjunctive_identities,
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

#[cfg(test)]
mod tests {
    use super::{tau_b, tau_b_cl, tau_star, tau_star_rule, val, valtz};
    use crate::syntax_tree::{asp::mini_gringo_cl as asp, fol::sigma_0 as fol};
    use indexmap::IndexSet;

    #[test]
    fn test_val() {
        for (term, var, target) in [
            (
                "X + 1",
                "Z1",
                "exists I$i J$i (Z1$g = I$i + J$i and I$i = X and J$i = 1)",
            ),
            (
                "3 - 5",
                "Z1",
                "exists I$i J$i (Z1$g = I$i - J$i and I$i = 3 and J$i = 5)",
            ),
            (
                "Xanadu/Yak",
                "Z1",
                "exists I$i J$i K$i (I$i = Xanadu and J$i = Yak and K$i * |J$i| <= |I$i| < (K$i + 1) * |J$i| and ((I$i * J$i >= 0 and Z1 = K$i) or (I$i * J$i < 0 and Z1 = -K$i)))",
            ),
            (
                "X \\ 3",
                "Z1",
                "exists I$i J$i K$i (I$i = X and J$i = 3 and K$i * |J$i| <= |I$i| < (K$i + 1) * |J$i| and ((I$i * J$i >= 0 and Z1 = I$i - K$i * J$i) or (I$i * J$i < 0 and Z1 = I$i + K$i * J$i)))",
            ),
            (
                "X..Y",
                "Z",
                "exists I$i J$i K$i (I$i = X and J$i = Y and Z$g = K$i and I$i <= K$i <= J$i)",
            ),
            (
                "X+1..Y",
                "Z1",
                "exists I$i J$i K$i ((exists I1$i J1$i (I$i = I1$i + J1$i and I1$i = X and J1$i = 1)) and J$i = Y and Z1 = K$i and I$i <= K$i <= J$i)",
            ),
        ] {
            let left = val(term.parse().unwrap(), var.parse().unwrap(), IndexSet::new());
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }

    #[test]
    fn test_valtz() {
        for (term, var, target) in [
            (
                "X + 1",
                "Z1",
                "exists I$i J$i (Z1$g = I$i + J$i and I$i = X and J$i = 1)",
            ),
            (
                "3 - (1..5)",
                "Z1",
                "exists I$i J$i (Z1$g = I$i - J$i and I$i = 3 and exists I1$i J1$i K1$i (I1$i = 1 and J1$i = 5 and J$i = K1$i and I1$i <= K1$i <= J1$i))",
            ),
        ] {
            let left = valtz(vec![term.parse().unwrap()], vec![var.parse().unwrap()]);
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }

    #[test]
    fn test_tau_b() {
        for (src, target) in [
            ("p(t)", "exists Z (Z = t and p(Z))"),
            ("not p(t)", "exists Z (Z = t and not p(Z))"),
            (
                "X < 1..5",
                "exists Z Z1 (Z = X and exists I$i J$i K$i (I$i = 1 and J$i = 5 and Z1 = K$i and I$i <= K$i <= J$i) and Z < Z1)",
            ),
            ("not not p(t)", "exists Z (Z = t and not not p(Z))"),
            ("not not x", "not not x"),
            (
                "not p(X,5)",
                "exists Z Z1 (Z = X and Z1 = 5 and not p(Z,Z1))",
            ),
            (
                "not p(X,0-5)",
                "exists Z Z1 (Z = X and exists I$i J$i (Z1 = I$i - J$i and I$i = 0 and J$i = 5) and not p(Z,Z1))",
            ),
            (
                "p(X,-1..5)",
                "exists Z Z1 (Z = X and exists I$i J$i K$i (I$i = -1 and J$i = 5 and Z1 = K$i and I$i <= K$i <= J$i) and p(Z,Z1))",
            ),
            (
                "p(X,-(1..5))",
                "exists Z Z1 (Z = X and exists I$i J$i (Z1 = I$i - J$i and I$i = 0 and exists I1$i J1$i K1$i (I1$i = 1 and J1$i = 5  and J$i = K1$i and I1$i <= K1$i <= J1$i)) and p(Z,Z1))",
            ),
            (
                "p(1/0)",
                "exists Z (exists I$i J$i K$i (I$i = 1 and J$i = 0 and (K$i * |J$i| <= |I$i| < (K$i+1) * |J$i|) and ((I$i * J$i >= 0 and Z = K$i) or (I$i*J$i < 0 and Z = -K$i)) ) and p(Z))",
            ),
        ] {
            let left = tau_b(src.parse().unwrap());
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }

    #[test]
    fn test_tau_b_cl() {
        for (src, target) in [
            (
                (
                    "q(X)",
                    IndexSet::from_iter(vec![asp::Variable("X".to_string())]),
                ),
                "exists Z (Z = X and q(Z))",
            ),
            (
                (
                    "not asg(V,I) : color(I)",
                    IndexSet::from_iter(vec![asp::Variable("V".to_string())]),
                ),
                "forall I (exists Z (Z = I and color(Z)) -> exists Z Z1 (Z = V and Z1 = I and not asg(Z, Z1)))",
            ),
            (
                (
                    "#false : p(X,Y), q(Y)",
                    IndexSet::from_iter(vec![
                        asp::Variable("X".to_string()),
                        asp::Variable("Y".to_string()),
                    ]),
                ),
                "(exists Z Z1 (Z = X and Z1 = Y and p(Z,Z1)) and exists Z (Z = Y and q(Z))) -> #false",
            ),
            (
                (
                    "not p(Z) : p(Z), X < Z, Z < Y",
                    IndexSet::from_iter(vec![
                        asp::Variable("X".to_string()),
                        asp::Variable("Y".to_string()),
                    ]),
                ),
                "forall Z ((exists Z1 (Z1 = Z and p(Z1)) and exists Z1 Z2 (Z1 = X and Z2 = Z and Z1 < Z2) and exists Z1 Z2 (Z1 = Z and Z2 = Y and Z1 < Z2)) -> exists Z1 (Z1 = Z and not p(Z1)) )",
            ),
            (
                (
                    "#false : p(Z), X < Z, Z < Y",
                    IndexSet::from_iter(vec![
                        asp::Variable("X".to_string()),
                        asp::Variable("Y".to_string()),
                    ]),
                ),
                "forall Z ((exists Z1 (Z1 = Z and p(Z1)) and exists Z1 Z2 (Z1 = X and Z2 = Z and Z1 < Z2) and exists Z1 Z2 (Z1 = Z and Z2 = Y and Z1 < Z2)) -> #false )",
            ),
            (
                (
                    "p(X,Y) : not q(X/Y)",
                    IndexSet::from_iter(vec![asp::Variable("X".to_string())]),
                ),
                "forall Y (exists Z (exists I$i J$i K$i (I$i = X and J$i = Y and (K$i * |J$i| <= |I$i| < (K$i+1) * |J$i|) and ((I$i * J$i >= 0 and Z = K$i) or (I$i*J$i < 0 and Z = -K$i)) ) and not q(Z)) -> exists Z Z1 (Z = X and Z1 = Y and p(Z, Z1)))",
            ),
        ] {
            let src = tau_b_cl(src.0.parse().unwrap(), &src.1);
            let target = target.parse().unwrap();
            assert_eq!(src, target, "{src} !=\n {target}")
        }
    }

    #[test]
    fn test_tau_star_rule() {
        for (src, target) in [
            (
                ("p(X) :- q(X,Y) : t(Y).", vec!["V".to_string()]),
                "forall V X (V = X and forall Y (exists Z (Z = Y and t(Z)) -> exists Z Z1 (Z = X and Z1 = Y and q(Z, Z1))) -> p(V))",
            ),
            (
                ("p(X) :- q(X,Y) : t(Y), 1 < X; t(X).", vec!["V".to_string()]),
                "forall V X (V = X and (forall Y (exists Z (Z = Y and t(Z)) and exists Z Z1 (Z = 1 and Z1 = X and Z < Z1) -> exists Z Z1 (Z = X and Z1 = Y and q(Z, Z1))) and exists Z (Z = X and t(Z))) -> p(V))",
            ),
            (
                ("p(X) :- q(X,Y) : t(Y), 1 < X, t(X).", vec!["V".to_string()]),
                "forall V X (V = X and (forall Y (exists Z (Z = Y and t(Z)) and exists Z Z1 (Z = 1 and Z1 = X and Z < Z1) and exists Z (Z = X and t(Z)) -> exists Z Z1 (Z = X and Z1 = Y and q(Z, Z1)))) -> p(V))",
            ),
            (
                ("p(X) :- q(X), t(X).", vec!["V".to_string()]),
                "forall V X (V = X and (exists Z (Z = X and q(Z)) and exists Z (Z = X and t(Z))) -> p(V))",
            ),
            (
                ("p(X) :- q(X); t(X).", vec!["V".to_string()]),
                "forall V X (V = X and (exists Z (Z = X and q(Z)) and exists Z (Z = X and t(Z))) -> p(V))",
            ),
            (
                ("p :- q(X).", vec![]),
                "forall X ( exists Z (Z = X and q(Z)) -> p)",
            ),
            (("p :- q : t; r.", vec![]), "((t -> q) and r) -> p"),
            (("p :- q : t, r.", vec![]), "(t and r -> q) -> p"),
            (("p :- s, q : t, r.", vec![]), "(s and (t and r -> q)) -> p"),
            (("p :- s; q : t, r.", vec![]), "(s and (t and r -> q)) -> p"),
            (
                ("p :- s; not not q : t, not r.", vec![]),
                "(s and (t and not r -> not not q)) -> p",
            ),
            (
                (
                    "sort(X,Y) :- p(X); p(Y); not p(Z) : p(Z), X < Z, Z < Y.",
                    vec!["V1".to_string(), "V2".to_string()],
                ),
                "forall V1 V2 X Y ( (V1 = X and V2 = Y and (exists Z (Z = X and p(Z)) and exists Z (Z = Y and p(Z)) and forall Z ((exists Z1 (Z1 = Z and p(Z1)) and exists Z1 Z2 (Z1 = X and Z2 = Z and Z1 < Z2) and exists Z1 Z2 (Z1 = Z and Z2 = Y and Z1 < Z2)) -> exists Z1 (Z1 = Z and not p(Z1)) ))) -> sort(V1,V2))",
            ),
        ] {
            let rule: asp::Rule = src.0.parse().unwrap();
            let src = fol::Theory {
                formulas: vec![tau_star_rule(rule, &src.1)],
            };
            let target = fol::Theory {
                formulas: vec![target.parse().unwrap()],
            };
            assert_eq!(src, target, "{src} != {target}")
        }
    }

    #[test]
    fn test_tau_star() {
        for (src, target) in [
            ("a:- b. a :- c.", "b -> a. c -> a."),
            (
                "p(a). p(b). q(X, Y) :- p(X), p(Y).",
                "forall V1 (V1 = a -> p(V1)). forall V1 (V1 = b -> p(V1)). forall V1 V2 X Y (V1 = X and V2 = Y and (exists Z (Z = X and p(Z)) and exists Z (Z = Y and p(Z))) -> q(V1,V2)).",
            ),
            ("p.", "#true -> p."),
            ("q :- not p.", "not p -> q."),
            (
                "{q(X)} :- p(X).",
                "forall V1 X (V1 = X and exists Z (Z = X and p(Z)) and not not q(V1) -> q(V1)).",
            ),
            (
                "{q(V)} :- p(V).",
                "forall V V1 (V1 = V and exists Z (Z = V and p(Z)) and not not q(V1) -> q(V1)).",
            ),
            (
                "{q(V+1)} :- p(V), not q(X).",
                "forall V V1 X (exists I$i J$i (V1 = I$i + J$i and I$i = V and J$i = 1) and (exists Z (Z = V and p(Z)) and exists Z (Z = X and not q(Z))) and not not q(V1) -> q(V1)).",
            ),
            (
                ":- p(X,3), not q(X,a).",
                "forall X (exists Z Z1 (Z = X and Z1 = 3 and p(Z,Z1)) and exists Z Z1 (Z = X and Z1 = a and not q(Z,Z1)) -> #false).",
            ),
            (":- p.", "p -> #false."),
            ("{p} :- q.", "q and not not p -> p."),
            ("{p}.", "not not p -> p."),
            ("{p(5)}.", "forall V1 (V1 = 5 and not not p(V1) -> p(V1))."),
            ("p. q.", "#true -> p. #true -> q."),
            (
                "{ra(X,a)} :- ta(X). ra(5,a).",
                "forall V1 V2 X (V1 = X and V2 = a and exists Z (Z = X and ta(Z)) and not not ra(V1, V2) -> ra(V1, V2)). forall V1 V2 (V1 = 5 and V2 = a -> ra(V1, V2)).",
            ),
            (
                "p :- X = 1..3 : q(X).",
                "forall X (exists Z (Z = X and q(Z)) -> exists Z Z1 (Z = X and exists I$i J$i K$i (I$i = 1 and J$i = 3 and Z1 = K$i and I$i <= K$i <= J$i) and Z = Z1)) -> p.",
            ),
            (
                "r(X) :- p(X,Y) : q(X,Y).",
                "forall V1 X (V1 = X and forall Y (exists Z Z1 (Z = X and Z1 = Y and q(Z, Z1)) -> exists Z Z1 (Z = X and Z1 = Y and p(Z, Z1))) -> r(V1)).",
            ),
        ] {
            let left = tau_star(src.parse().unwrap());
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }
}
