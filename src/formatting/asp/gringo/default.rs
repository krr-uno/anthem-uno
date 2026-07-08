use {
    crate::{
        formatting::{Associativity, Precedence},
        syntax_tree::{
            Node,
            asp::gringo::{
                Atom, AtomicFormula, BinaryOperator, Body, BodyLiteral, Comparison,
                ConditionalBody, ConditionalHead, Head, Literal, PrecomputedTerm, Predicate,
                Program, Relation, Rule, Sign, Term, UnaryOperator, Variable,
            },
        },
    },
    std::fmt::{self, Display, Formatter},
};

pub struct Format<'a, N: Node>(pub &'a N);

impl Display for Format<'_, PrecomputedTerm> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            PrecomputedTerm::Infimum => write!(f, "#inf"),
            PrecomputedTerm::Numeral(n) => write!(f, "{n}"),
            PrecomputedTerm::Symbol(s) => write!(f, "{s}"),
            PrecomputedTerm::Supremum => write!(f, "#sup"),
        }
    }
}

impl Display for Format<'_, Variable> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match &self.0.name {
            Some(name) => write!(f, "{}", name),
            None => write!(f, "_"),
        }
    }
}

impl Display for Format<'_, UnaryOperator> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            UnaryOperator::Negative => write!(f, "-"),
            UnaryOperator::AbsoluteValue => write!(f, "|"),
        }
    }
}

impl Display for Format<'_, BinaryOperator> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            BinaryOperator::Add => write!(f, "+"),
            BinaryOperator::Subtract => write!(f, "-"),
            BinaryOperator::Multiply => write!(f, "*"),
            BinaryOperator::Divide => write!(f, "/"),
            BinaryOperator::DivideInteger => write!(f, "//"),
            BinaryOperator::Modulo => write!(f, "\\"),
            BinaryOperator::ModuloInteger => write!(f, "@"),
            BinaryOperator::Interval => write!(f, ".."),
        }
    }
}

impl Precedence for Format<'_, Term> {
    fn precedence(&self) -> usize {
        match self.0 {
            Term::PrecomputedTerm(PrecomputedTerm::Numeral(1..)) => 1,
            Term::UnaryOperation { .. } | Term::PrecomputedTerm(_) | Term::Variable(_) => 0,
            Term::BinaryOperation {
                op:
                    BinaryOperator::Multiply
                    | BinaryOperator::Divide
                    | BinaryOperator::DivideInteger
                    | BinaryOperator::Modulo
                    | BinaryOperator::ModuloInteger,
                ..
            } => 2,
            Term::BinaryOperation {
                op: BinaryOperator::Add | BinaryOperator::Subtract,
                ..
            } => 3,
            Term::BinaryOperation {
                op: BinaryOperator::Interval,
                ..
            } => 4,
        }
    }

    fn associativity(&self) -> Associativity {
        Associativity::Left
    }

    fn fmt_operator(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Term::UnaryOperation { op, .. } => write!(f, "{}", Format(op)),
            Term::BinaryOperation { op, .. } => match op {
                BinaryOperator::Interval => write!(f, "{}", Format(op)),
                _ => write!(f, " {} ", Format(op)),
            },
            Term::PrecomputedTerm(_) | Term::Variable(_) => unreachable!(),
        }
    }
}

impl Display for Format<'_, Term> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Term::PrecomputedTerm(c) => Format(c).fmt(f),
            Term::Variable(v) => Format(v).fmt(f),
            Term::UnaryOperation {
                op: UnaryOperator::Negative,
                arg,
            } => self.fmt_unary(Format(arg.as_ref()), f),
            Term::UnaryOperation {
                op: UnaryOperator::AbsoluteValue,
                arg,
            } => write!(
                f,
                "{}{}{}",
                Format(&UnaryOperator::AbsoluteValue),
                Format(arg.as_ref()),
                Format(&UnaryOperator::AbsoluteValue)
            ),
            Term::BinaryOperation { lhs, rhs, .. } => {
                self.fmt_binary(Format(lhs.as_ref()), Format(rhs.as_ref()), f)
            }
        }
    }
}

impl Display for Format<'_, Predicate> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let symbol = &self.0.symbol;
        let arity = &self.0.arity;
        write!(f, "{symbol}/{arity}")
    }
}

impl Display for Format<'_, Atom> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let predicate = &self.0.predicate_symbol;
        let terms = &self.0.terms;

        write!(f, "{predicate}")?;

        if !terms.is_empty() {
            let mut iter = terms.iter().map(Format);
            write!(f, "({}", iter.next().unwrap())?;
            for term in iter {
                write!(f, ", {term}")?;
            }
            write!(f, ")")?;
        }

        Ok(())
    }
}

impl Display for Format<'_, Program> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for rule in &self.0.rules {
            writeln!(f, "{}", Format(rule))?;
        }
        Ok(())
    }
}

impl Display for Format<'_, Sign> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Sign::NoSign => write!(f, ""),
            Sign::Negation => write!(f, "not"),
            Sign::DoubleNegation => write!(f, "not not"),
        }
    }
}

impl Display for Format<'_, Literal> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.0.sign == Sign::NoSign {
            write!(f, "{}", Format(&self.0.atom))
        } else {
            write!(f, "{} {}", Format(&self.0.sign), Format(&self.0.atom))
        }
    }
}

impl Display for Format<'_, Relation> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Relation::Equal => write!(f, "="),
            Relation::NotEqual => write!(f, "!="),
            Relation::Less => write!(f, "<"),
            Relation::LessEqual => write!(f, "<="),
            Relation::Greater => write!(f, ">"),
            Relation::GreaterEqual => write!(f, ">="),
        }
    }
}

impl Display for Format<'_, Comparison> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {}",
            Format(&self.0.lhs),
            Format(&self.0.relation),
            Format(&self.0.rhs)
        )
    }
}

impl Display for Format<'_, AtomicFormula> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            AtomicFormula::Literal(l) => write!(f, "{}", Format(l)),
            AtomicFormula::Comparison(c) => write!(f, "{}", Format(c)),
        }
    }
}

impl Display for Format<'_, ConditionalHead> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            ConditionalHead::AtomicFormula(a) => write!(f, "{}", Format(a)),
            ConditionalHead::Falsity => write!(f, "#false"),
        }
    }
}

impl Display for Format<'_, ConditionalBody> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut iter = self.0.formulas.iter().map(Format);
        if let Some(formula) = iter.next() {
            write!(f, "{formula}")?;
            for formula in iter {
                write!(f, "; {formula}")?;
            }
        }
        Ok(())
    }
}

impl Display for Format<'_, BodyLiteral> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            BodyLiteral::GfiveConditionalLiteral(cl) => {
                write!(f, "{}", Format(&cl.head))?;
                if !cl.conditions.formulas.is_empty() {
                    write!(f, " : {}", Format(&cl.conditions))?;
                }
            }
            BodyLiteral::GsixConditionalLiteral(cl) => {
                write!(f, "{}", Format(&cl.head))?;
                if !cl.conditions.formulas.is_empty() {
                    write!(f, " :: {}", Format(&cl.conditions))?;
                }
            }
        }
        Ok(())
    }
}

impl Display for Format<'_, Head> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Head::Basic(a) => write!(f, "{}", Format(a)),
            Head::Choice(a) => write!(f, "{{{}}}", Format(a)),
            Head::Falsity => write!(f, ""),
        }
    }
}

impl Display for Format<'_, Body> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut iter = self.0.formulas.iter().map(Format);
        if let Some(formula) = iter.next() {
            write!(f, "{formula}")?;
            for formula in iter {
                write!(f, ", {formula}")?;
            }
        }
        Ok(())
    }
}

impl Display for Format<'_, Rule> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Format(&self.0.head))?;
        if self.0.head == Head::Falsity || !self.0.body.formulas.is_empty() {
            write!(f, " :- ")?;
        }
        write!(f, "{}.", Format(&self.0.body))
    }
}
