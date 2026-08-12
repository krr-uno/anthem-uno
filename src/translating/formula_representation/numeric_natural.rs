use crate::{
    command_line::arguments::Dialect,
    syntax_tree::{
        asp::mini_gringo as asp,
        fol::sigma_0::{
            self as fol, Formula, GeneralTerm, Guard, IntegerTerm, Sort, SymbolicTerm, Theory,
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
            "forall I$ J$ R$ ( moduloGraph(I$,J$,R$) <-> exists Q$ (I$ = J$ * Q$ + R$ & J$ != 0 & 0 <= R$ < J$) )".parse().unwrap()
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
// of an arithmetic operator
fn p2f(t: asp::Term, scope: bool) -> GeneralTerm {
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
                terms: terms.into_iter().map(|t| p2f(t, false)).collect(),
            })
        }

        asp::Term::Variable(v) => {
            if scope {
                GeneralTerm::IntegerTerm(IntegerTerm::Variable(v.0))
            } else {
                GeneralTerm::Variable(v.0)
            }
        }

        asp::Term::UnaryOperation { op, arg } => {
            let gen_term = p2f(*arg, true);
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

            let gen_lhs = p2f(*lhs, true);
            let lhs = match gen_lhs {
                GeneralTerm::IntegerTerm(integer_term) => integer_term,
                _ => unreachable!("the expression {gen_lhs} is not in numeric normal form"),
            };

            let gen_rhs = p2f(*rhs, true);
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
// 2) the left-hand side of an equation that contains an indefinite function symbol
// in the right-hand side to the integer sort
fn nu_literal(f: asp::AtomicFormula) -> Formula {
    match f {
        asp::AtomicFormula::Literal(l) => {
            let sign = l.sign;

            let atom = Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
                predicate_symbol: l.atom.predicate_symbol,
                terms: l.atom.terms.into_iter().map(|t| p2f(t, false)).collect(),
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
                let terms = vec![p2f(t1, true), p2f(t2, true), p2f(c.lhs, false)];
                Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
                    predicate_symbol,
                    terms,
                }))
            } else {
                Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                    term: p2f(c.lhs, false),
                    guards: vec![Guard {
                        relation: c.relation.into(),
                        term: p2f(c.rhs, false),
                    }],
                }))
            }
        }
    }
}

fn nu_rule(r: asp::Rule) -> Formula {
    let body = Formula::conjoin(r.body.formulas.into_iter().map(nu_literal));

    let head = match r.head {
        asp::Head::Basic(atom) => nu_literal(asp::AtomicFormula::Literal(asp::Literal {
            sign: asp::Sign::NoSign,
            atom,
        })),
        asp::Head::Falsity => Formula::AtomicFormula(fol::AtomicFormula::Falsity),
        asp::Head::Choice(_) => {
            unreachable!("choice rules are abbreviations in numeric normal form")
        }
    };

    Formula::BinaryFormula {
        connective: fol::BinaryConnective::Implication,
        lhs: body.into(),
        rhs: head.into(),
    }
    .universal_closure()
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
