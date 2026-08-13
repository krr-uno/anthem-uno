use indexmap::IndexSet;

use crate::{
    command_line::arguments::Dialect,
    syntax_tree::{
        asp::mini_gringo as asp,
        fol::sigma_0::{
            self as fol, Formula, GeneralTerm, Guard, IntegerTerm, Quantification, Sort,
            SymbolicTerm, Theory,
        },
    },
};

enum IndefiniteFunction {
    Division,
    Modulo,
    Interval,
}

fn construct_graphf_axiom(f: IndefiniteFunction, d: Dialect) -> fol::Formula {
    match (f, d) {
        (IndefiniteFunction::Division, Dialect::GringoFive) => {
            "forall I$ J$ Z$ ( divisionGraph(I$,J$,Z$) <->
                exists K$ (
                    K$ * |J$| <= |I$| < (K$+1) * |J$| and
                    ((I$ * J$ >= 0 and Z$ = K$) or (I$ * J$ < 0 and Z$ = -K$))))".parse().unwrap()
        },
        (IndefiniteFunction::Modulo, Dialect::GringoFive) => {
            "forall I$ J$ Z$ ( moduloGraph(I$,J$,Z$) <->
                exists K$ (
                    K$ * |J$| <= |I$| < (K$+1) * |J$| and
                    ((I$ * J$ >= 0 and Z$ = I$ - K$ * J$) or (I$ * J$ < 0 and Z$ = I$ + K$ * J$))))".parse().unwrap()
        },
        (IndefiniteFunction::Division, Dialect::GringoSix) => {
            "forall I$ J$ Q$ ( divisionGraph(I$,J$,Q$) <-> exists R$ (I$ = J$ * Q$ + R$ and J$ != 0 and 0 <= R$ < J$) )".parse().unwrap()
        },
        (IndefiniteFunction::Modulo, Dialect::GringoSix) => {
            "forall I$ J$ R$ ( moduloGraph(I$,J$,R$) <-> exists Q$ (I$ = J$ * Q$ + R$ and J$ != 0 and 0 <= R$ < J$) )".parse().unwrap()
        },
        (IndefiniteFunction::Interval, _) => {
            "forall I$ J$ K$ ( intervalGraph(I$,J$,K$) <-> I$ <= K$ <= J$ )".parse().unwrap()
        },
    }
}

impl From<asp::BasicSymbol> for GeneralTerm {
    fn from(value: asp::BasicSymbol) -> Self {
        match value {
            asp::BasicSymbol::Infimum => GeneralTerm::Infimum,
            asp::BasicSymbol::Numeral(n) => GeneralTerm::IntegerTerm(IntegerTerm::Numeral(n)),
            asp::BasicSymbol::Symbol(s) => GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol(s)),
            asp::BasicSymbol::Supremum => GeneralTerm::Supremum,
        }
    }
}

impl From<asp::UnaryOperator> for fol::UnaryOperator {
    fn from(value: asp::UnaryOperator) -> Self {
        match value {
            asp::UnaryOperator::Negative => fol::UnaryOperator::Negative,
        }
    }
}

// Convert top-level general variables in the term to
// an integer variable of the same name if within the scope
// of an arithmetic operator.
// Keeps track of which variables have their sort changed via 'vars'
fn p2f(t: asp::Term, scope: bool, vars: &mut IndexSet<String>) -> GeneralTerm {
    match t {
        asp::Term::BasicSymbol(b) => {
            if scope {
                match b {
                    asp::BasicSymbol::Numeral(n) => {
                        GeneralTerm::IntegerTerm(IntegerTerm::Numeral(n))
                    }
                    _ => unreachable!(
                        "the only basic symbols allowed in the scope of arithmetic operators are numerals"
                    ),
                }
            } else {
                GeneralTerm::from(b)
            }
        }

        asp::Term::HerbrandFunction { symbol, terms } => {
            if scope {
                panic!("constructors should not occur within the scope of an arithmetic operation");
            }
            GeneralTerm::Function(fol::Function {
                function_symbol: symbol,
                sort: Sort::Symbol,
                terms: terms.into_iter().map(|t| p2f(t, false, vars)).collect(),
            })
        }

        asp::Term::Variable(v) => {
            if scope {
                let varname = v.0;
                vars.insert(varname.clone());
                GeneralTerm::IntegerTerm(IntegerTerm::Variable(varname))
            } else {
                GeneralTerm::Variable(v.0)
            }
        }

        asp::Term::UnaryOperation { op, arg } => {
            let gen_term = p2f(*arg, true, vars);
            let inner = match gen_term {
                GeneralTerm::IntegerTerm(integer_term) => integer_term,
                _ => unreachable!("the expression {gen_term} is not in numeric normal form"),
            };

            GeneralTerm::IntegerTerm(IntegerTerm::UnaryOperation {
                op: fol::UnaryOperator::from(op),
                arg: inner.into(),
            })
        }

        asp::Term::BinaryOperation { op, lhs, rhs } => {
            let operation = match op {
                asp::BinaryOperator::Add => fol::BinaryOperator::Add,
                asp::BinaryOperator::Subtract => fol::BinaryOperator::Subtract,
                asp::BinaryOperator::Multiply => fol::BinaryOperator::Multiply,
                _ => unreachable!(
                    "term is not in numeric normal form due to presence of indefinite functions"
                ),
            };

            let gen_lhs = p2f(*lhs, true, vars);
            let lhs = match gen_lhs {
                GeneralTerm::IntegerTerm(integer_term) => integer_term,
                _ => unreachable!("the expression {gen_lhs} is not in numeric normal form"),
            };

            let gen_rhs = p2f(*rhs, true, vars);
            let rhs = match gen_rhs {
                GeneralTerm::IntegerTerm(integer_term) => integer_term,
                _ => unreachable!("the expression {gen_rhs} is not in numeric normal form"),
            };

            GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                op: operation,
                lhs: lhs.into(),
                rhs: rhs.into(),
            })
        }
    }
}

// Change the sort of every variable that occurs in
// 1) the scope of an arithmetic operation, or
// 2) the left-hand side of an equation that contains an indefinite function symbol in the right-hand side
// to the integer sort
fn nu_literal(f: asp::AtomicFormula, vars: &mut IndexSet<String>) -> Formula {
    match f {
        asp::AtomicFormula::Literal(l) => {
            let sign = l.sign;

            let atom = Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
                predicate_symbol: l.atom.predicate_symbol,
                terms: l
                    .atom
                    .terms
                    .into_iter()
                    .map(|t| p2f(t, false, vars))
                    .collect(),
            }));

            match sign {
                asp::Sign::NoSign => atom,
                asp::Sign::Negation => Formula::UnaryFormula {
                    connective: fol::UnaryConnective::Negation,
                    formula: atom.into(),
                },
                asp::Sign::DoubleNegation => Formula::UnaryFormula {
                    connective: fol::UnaryConnective::Negation,
                    formula: Formula::UnaryFormula {
                        connective: fol::UnaryConnective::Negation,
                        formula: atom.into(),
                    }
                    .into(),
                },
            }
        }
        asp::AtomicFormula::Comparison(c) => {
            if c.clone().indefinite_equality() {
                let (binop, t1, t2) = c.rhs.destructure_binary_operation().unwrap();
                let predicate_symbol = match binop {
                    asp::BinaryOperator::Divide => String::from("divisionGraph"),
                    asp::BinaryOperator::Modulo => String::from("moduloGraph"),
                    asp::BinaryOperator::Interval => String::from("intervalGraph"),
                    _ => unreachable!("an indefinite equality cannot contain definite functions"),
                };
                // c.lhs is "within arithmetic scope" since it falls in case 2
                let terms = vec![
                    p2f(t1, true, vars),
                    p2f(t2, true, vars),
                    p2f(c.lhs, true, vars),
                ];
                Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
                    predicate_symbol,
                    terms,
                }))
            } else {
                Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                    term: p2f(c.lhs, false, vars),
                    guards: vec![Guard {
                        relation: c.relation.into(),
                        term: p2f(c.rhs, false, vars),
                    }],
                }))
            }
        }
    }
}

fn nu_rule(r: asp::Rule) -> Formula {
    // The set of variables from the rule whose
    // sort has been changed to "integer" in at least one term
    let mut resorted_variables = IndexSet::new();

    let body = Formula::conjoin(
        r.body
            .formulas
            .into_iter()
            .map(|f| nu_literal(f, &mut resorted_variables)),
    );

    let head = match r.head {
        asp::Head::Basic(atom) => nu_literal(
            asp::AtomicFormula::Literal(asp::Literal {
                sign: asp::Sign::NoSign,
                atom,
            }),
            &mut resorted_variables,
        ),
        asp::Head::Falsity => Formula::AtomicFormula(fol::AtomicFormula::Falsity),
        asp::Head::Choice(_) => {
            unreachable!("choice rules are abbreviations in numeric normal form")
        }
    };

    let partially_naturalized_rule = Formula::BinaryFormula {
        connective: fol::BinaryConnective::Implication,
        lhs: body.into(),
        rhs: head.into(),
    };

    unify_variable_sorts(partially_naturalized_rule, &resorted_variables).universal_closure()
}

fn unify_variable_sorts_term(t: GeneralTerm, vars: &IndexSet<String>) -> GeneralTerm {
    match t {
        GeneralTerm::Variable(v) => {
            if vars.contains(&v) {
                GeneralTerm::IntegerTerm(IntegerTerm::Variable(v))
            } else {
                GeneralTerm::Variable(v)
            }
        }
        // GeneralTerm::IntegerTerm(i) => match i {
        //     IntegerTerm::Numeral(n) => GeneralTerm::IntegerTerm(IntegerTerm::Numeral(n)),
        //     IntegerTerm::FunctionConstant(c) => GeneralTerm::IntegerTerm(IntegerTerm::FunctionConstant(c)),
        //     IntegerTerm::Variable(v) => GeneralTerm::IntegerTerm(IntegerTerm::Variable(v)),
        //     IntegerTerm::UnaryOperation { op, arg } => GeneralTerm::IntegerTerm(
        //         IntegerTerm::UnaryOperation { op, arg }
        //     ),
        //     IntegerTerm::BinaryOperation { op, lhs, rhs } => GeneralTerm::IntegerTerm(
        //         IntegerTerm::BinaryOperation { op, lhs, rhs }
        //     ),
        // },
        GeneralTerm::SymbolicTerm(s) => match s {
            SymbolicTerm::Variable(v) => {
                if vars.contains(&v) {
                    GeneralTerm::IntegerTerm(IntegerTerm::Variable(v))
                } else {
                    GeneralTerm::SymbolicTerm(SymbolicTerm::Variable(v))
                }
            }
            x => GeneralTerm::SymbolicTerm(x),
        },
        GeneralTerm::Function(f) => GeneralTerm::Function(fol::Function {
            function_symbol: f.function_symbol,
            sort: f.sort,
            terms: f
                .terms
                .into_iter()
                .map(|t| unify_variable_sorts_term(t, vars))
                .collect(),
        }),
        x => x,
    }
}

fn unify_variable_sorts_atomic(
    f: fol::AtomicFormula,
    vars: &IndexSet<String>,
) -> fol::AtomicFormula {
    match f {
        fol::AtomicFormula::Truth => fol::AtomicFormula::Truth,
        fol::AtomicFormula::Falsity => fol::AtomicFormula::Falsity,
        fol::AtomicFormula::Atom(atom) => fol::AtomicFormula::Atom(fol::Atom {
            predicate_symbol: atom.predicate_symbol,
            terms: atom
                .terms
                .into_iter()
                .map(|t| unify_variable_sorts_term(t, vars))
                .collect(),
        }),
        fol::AtomicFormula::Comparison(comparison) => {
            fol::AtomicFormula::Comparison(fol::Comparison {
                term: unify_variable_sorts_term(comparison.term, vars),
                guards: comparison
                    .guards
                    .into_iter()
                    .map(|g| Guard {
                        relation: g.relation,
                        term: unify_variable_sorts_term(g.term, vars),
                    })
                    .collect(),
            })
        }
    }
}

// Sets every occurrence of a variable whose name occurs in 'vars'
// to an integer-sorted variable of the same name
fn unify_variable_sorts(f: Formula, vars: &IndexSet<String>) -> Formula {
    match f {
        Formula::AtomicFormula(a) => Formula::AtomicFormula(unify_variable_sorts_atomic(a, vars)),
        Formula::UnaryFormula {
            connective,
            formula,
        } => Formula::UnaryFormula {
            connective,
            formula: unify_variable_sorts(*formula, vars).into(),
        },
        Formula::BinaryFormula {
            connective,
            lhs,
            rhs,
        } => Formula::BinaryFormula {
            connective,
            lhs: unify_variable_sorts(*lhs, vars).into(),
            rhs: unify_variable_sorts(*rhs, vars).into(),
        },
        Formula::QuantifiedFormula {
            quantification:
                Quantification {
                    quantifier,
                    variables,
                },
            formula,
        } => {
            let new_variables = variables
                .into_iter()
                .map(|v| {
                    let name = v.name.clone();
                    if vars.contains(&name) {
                        fol::Variable {
                            name,
                            sort: Sort::Integer,
                        }
                    } else {
                        v
                    }
                })
                .collect();

            Formula::QuantifiedFormula {
                quantification: Quantification {
                    quantifier,
                    variables: new_variables,
                },
                formula: unify_variable_sorts(*formula, vars).into(),
            }
        }
    }
}

// Requires a numeric normal form program as input
pub(crate) fn numeric_natural(p: asp::Program, d: Dialect) -> Theory {
    let mut formulas = Vec::new();

    let indefinites = p.indefinite_functions();
    if indefinites.contains(&asp::BinaryOperator::Divide) {
        formulas.push(construct_graphf_axiom(IndefiniteFunction::Division, d));
    }
    if indefinites.contains(&asp::BinaryOperator::Modulo) {
        formulas.push(construct_graphf_axiom(IndefiniteFunction::Modulo, d));
    }
    if indefinites.contains(&asp::BinaryOperator::Interval) {
        formulas.push(construct_graphf_axiom(IndefiniteFunction::Interval, d));
    }

    for rule in p.rules {
        formulas.push(nu_rule(rule));
    }

    Theory { formulas }
}
