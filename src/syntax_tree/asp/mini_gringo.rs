use {
    crate::{
        formatting::asp::mini_gringo::default::Format,
        parsing::asp::mini_gringo::pest::{
            AtomParser, AtomicFormulaParser, BinaryOperatorParser, BodyParser, ComparisonParser,
            HeadParser, LiteralParser, PrecomputedTermParser, PredicateParser, ProgramParser,
            RelationParser, RuleParser, SignParser, TermParser, UnaryOperatorParser,
            VariableParser,
        },
        syntax_tree::{
            Node,
            asp::{self, mini_gringo_cl},
            impl_node,
        },
    },
    derive_more::derive::IntoIterator,
    indexmap::IndexSet,
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum PrecomputedTerm {
    Infimum,
    Numeral(isize),
    Symbol(String),
    Supremum,
}

impl PrecomputedTerm {
    pub fn function_constants(&self) -> IndexSet<String> {
        match &self {
            PrecomputedTerm::Infimum => IndexSet::new(),
            PrecomputedTerm::Numeral(_) => IndexSet::new(),
            PrecomputedTerm::Symbol(s) => IndexSet::from([s.clone()]),
            PrecomputedTerm::Supremum => IndexSet::new(),
        }
    }
}

impl_node!(PrecomputedTerm, Format, PrecomputedTermParser);

impl From<asp::mini_gringo_cl::PrecomputedTerm> for PrecomputedTerm {
    fn from(value: asp::mini_gringo_cl::PrecomputedTerm) -> Self {
        match value {
            asp::mini_gringo_cl::PrecomputedTerm::Infimum => PrecomputedTerm::Infimum,
            asp::mini_gringo_cl::PrecomputedTerm::Numeral(n) => PrecomputedTerm::Numeral(n),
            asp::mini_gringo_cl::PrecomputedTerm::Symbol(s) => PrecomputedTerm::Symbol(s),
            asp::mini_gringo_cl::PrecomputedTerm::Supremum => PrecomputedTerm::Supremum,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Variable(pub String);

impl_node!(Variable, Format, VariableParser);

impl From<asp::mini_gringo_cl::Variable> for Variable {
    fn from(value: asp::mini_gringo_cl::Variable) -> Self {
        Variable(value.0)
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum UnaryOperator {
    Negative,
}

impl_node!(UnaryOperator, Format, UnaryOperatorParser);

impl TryFrom<mini_gringo_cl::UnaryOperator> for UnaryOperator {
    type Error = &'static str;

    fn try_from(value: mini_gringo_cl::UnaryOperator) -> Result<Self, Self::Error> {
        match value {
            mini_gringo_cl::UnaryOperator::Negative => Ok(UnaryOperator::Negative),
            mini_gringo_cl::UnaryOperator::AbsoluteValue => {
                Err("mini-gringo programs do not support absolute values")
            }
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum BinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    DivideInteger,
    Modulo,
    ModuloInteger,
    Interval,
}

impl_node!(BinaryOperator, Format, BinaryOperatorParser);

impl From<asp::mini_gringo_cl::BinaryOperator> for BinaryOperator {
    fn from(value: asp::mini_gringo_cl::BinaryOperator) -> Self {
        match value {
            mini_gringo_cl::BinaryOperator::Add => BinaryOperator::Add,
            mini_gringo_cl::BinaryOperator::Subtract => BinaryOperator::Subtract,
            mini_gringo_cl::BinaryOperator::Multiply => BinaryOperator::Multiply,
            mini_gringo_cl::BinaryOperator::Divide => BinaryOperator::Divide,
            mini_gringo_cl::BinaryOperator::DivideInteger => BinaryOperator::DivideInteger,
            mini_gringo_cl::BinaryOperator::Modulo => BinaryOperator::Modulo,
            mini_gringo_cl::BinaryOperator::ModuloInteger => BinaryOperator::ModuloInteger,
            mini_gringo_cl::BinaryOperator::Interval => BinaryOperator::Interval,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Term {
    PrecomputedTerm(PrecomputedTerm),
    Variable(Variable),
    UnaryOperation {
        op: UnaryOperator,
        arg: Box<Term>,
    },
    BinaryOperation {
        op: BinaryOperator,
        lhs: Box<Term>,
        rhs: Box<Term>,
    },
}

impl_node!(Term, Format, TermParser);

impl TryFrom<mini_gringo_cl::Term> for Term {
    type Error = &'static str;

    fn try_from(value: mini_gringo_cl::Term) -> Result<Self, Self::Error> {
        match value {
            mini_gringo_cl::Term::PrecomputedTerm(t) => Ok(Term::PrecomputedTerm(t.into())),
            mini_gringo_cl::Term::Variable(v) => Ok(Term::Variable(v.into())),
            mini_gringo_cl::Term::UnaryOperation {
                op: op_cl,
                arg: arg_cl,
            } => {
                let op: UnaryOperator = op_cl.try_into()?;
                let arg_mg: Term = (*arg_cl).try_into()?;
                Ok(Self::UnaryOperation {
                    op,
                    arg: arg_mg.into(),
                })
            }
            mini_gringo_cl::Term::BinaryOperation {
                op: op_cl,
                lhs: lhs_cl,
                rhs: rhs_cl,
            } => {
                let op: BinaryOperator = op_cl.into();
                let lhs_mg: Term = (*lhs_cl).try_into()?;
                let rhs_mg: Term = (*rhs_cl).try_into()?;

                Ok(Self::BinaryOperation {
                    op,
                    lhs: lhs_mg.into(),
                    rhs: rhs_mg.into(),
                })
            }
        }
    }
}

impl Term {
    pub fn variables(&self) -> IndexSet<Variable> {
        match &self {
            Term::PrecomputedTerm(_) => IndexSet::new(),
            Term::Variable(v) => IndexSet::from([v.clone()]),
            Term::UnaryOperation { arg, .. } => arg.variables(),
            Term::BinaryOperation { lhs, rhs, .. } => {
                let mut vars = lhs.variables();
                vars.extend(rhs.variables());
                vars
            }
        }
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        match &self {
            Term::PrecomputedTerm(t) => t.function_constants(),
            Term::Variable(_) => IndexSet::new(),
            Term::UnaryOperation { arg, .. } => arg.function_constants(),
            Term::BinaryOperation { lhs, rhs, .. } => {
                let mut functions = lhs.function_constants();
                functions.extend(rhs.function_constants());
                functions
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Predicate {
    pub symbol: String,
    pub arity: usize,
}

impl_node!(Predicate, Format, PredicateParser);

impl From<crate::syntax_tree::fol::sigma_0::Predicate> for Predicate {
    fn from(value: crate::syntax_tree::fol::sigma_0::Predicate) -> Self {
        Predicate {
            symbol: value.symbol,
            arity: value.arity,
        }
    }
}

impl From<crate::syntax_tree::GenericPredicate> for Predicate {
    fn from(value: crate::syntax_tree::GenericPredicate) -> Self {
        Predicate {
            symbol: value.symbol,
            arity: value.arity,
        }
    }
}

impl From<asp::mini_gringo_cl::Predicate> for Predicate {
    fn from(value: asp::mini_gringo_cl::Predicate) -> Self {
        Predicate {
            symbol: value.symbol,
            arity: value.arity,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Atom {
    pub predicate_symbol: String,
    pub terms: Vec<Term>,
}

impl_node!(Atom, Format, AtomParser);

impl Atom {
    pub fn predicate(&self) -> Predicate {
        Predicate {
            symbol: self.predicate_symbol.clone(),
            arity: self.terms.len(),
        }
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = IndexSet::new();
        for term in self.terms.iter() {
            vars.extend(term.variables())
        }
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut functions = IndexSet::new();
        for term in self.terms.iter() {
            functions.extend(term.function_constants())
        }
        functions
    }
}

impl TryFrom<mini_gringo_cl::Atom> for Atom {
    type Error = &'static str;

    fn try_from(value: mini_gringo_cl::Atom) -> Result<Self, Self::Error> {
        let mut mg_terms = Vec::new();
        for term in value.terms {
            let t = Term::try_from(term)?;
            mg_terms.push(t);
        }

        Ok(Atom {
            predicate_symbol: value.predicate_symbol,
            terms: mg_terms,
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Sign {
    NoSign,
    Negation,
    DoubleNegation,
}

impl_node!(Sign, Format, SignParser);

impl From<mini_gringo_cl::Sign> for Sign {
    fn from(value: mini_gringo_cl::Sign) -> Self {
        match value {
            mini_gringo_cl::Sign::NoSign => Sign::NoSign,
            mini_gringo_cl::Sign::Negation => Sign::Negation,
            mini_gringo_cl::Sign::DoubleNegation => Sign::DoubleNegation,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Literal {
    pub sign: Sign,
    pub atom: Atom,
}

impl_node!(Literal, Format, LiteralParser);

impl Literal {
    pub fn predicate(&self) -> Predicate {
        self.atom.predicate()
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        self.atom.variables()
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        self.atom.function_constants()
    }
}

impl TryFrom<mini_gringo_cl::Literal> for Literal {
    type Error = &'static str;

    fn try_from(value: mini_gringo_cl::Literal) -> Result<Self, Self::Error> {
        match Atom::try_from(value.atom) {
            Ok(atom) => Ok(Literal {
                sign: value.sign.into(),
                atom,
            }),
            Err(e) => Err(e),
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum Relation {
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

impl_node!(Relation, Format, RelationParser);

impl From<asp::mini_gringo_cl::Relation> for Relation {
    fn from(value: asp::mini_gringo_cl::Relation) -> Self {
        match value {
            mini_gringo_cl::Relation::Equal => Relation::Equal,
            mini_gringo_cl::Relation::NotEqual => Relation::NotEqual,
            mini_gringo_cl::Relation::Less => Relation::Less,
            mini_gringo_cl::Relation::LessEqual => Relation::LessEqual,
            mini_gringo_cl::Relation::Greater => Relation::Greater,
            mini_gringo_cl::Relation::GreaterEqual => Relation::GreaterEqual,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Comparison {
    pub relation: Relation,
    pub lhs: Term,
    pub rhs: Term,
}

impl_node!(Comparison, Format, ComparisonParser);

impl Comparison {
    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = self.lhs.variables();
        vars.extend(self.rhs.variables());
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut functions = self.lhs.function_constants();
        functions.extend(self.rhs.function_constants());
        functions
    }
}

impl TryFrom<mini_gringo_cl::Comparison> for Comparison {
    type Error = &'static str;

    fn try_from(value: mini_gringo_cl::Comparison) -> Result<Self, Self::Error> {
        let lhs: Term = value.lhs.try_into()?;
        let rhs: Term = value.rhs.try_into()?;
        Ok(Comparison {
            relation: value.relation.into(),
            lhs,
            rhs,
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum AtomicFormula {
    Literal(Literal),
    Comparison(Comparison),
}

impl_node!(AtomicFormula, Format, AtomicFormulaParser);

impl AtomicFormula {
    pub fn variables(&self) -> IndexSet<Variable> {
        match &self {
            AtomicFormula::Literal(l) => l.variables(),
            AtomicFormula::Comparison(c) => c.variables(),
        }
    }

    pub fn predicates(&self) -> IndexSet<Predicate> {
        match &self {
            AtomicFormula::Literal(l) => IndexSet::from([l.predicate()]),
            AtomicFormula::Comparison(_) => IndexSet::new(),
        }
    }

    fn positive_predicates(&self) -> IndexSet<Predicate> {
        match &self {
            AtomicFormula::Literal(Literal {
                sign: Sign::NoSign,
                atom,
            }) => IndexSet::from([atom.predicate()]),
            AtomicFormula::Literal(_) | AtomicFormula::Comparison(_) => IndexSet::new(),
        }
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        match &self {
            AtomicFormula::Literal(l) => l.function_constants(),
            AtomicFormula::Comparison(c) => c.function_constants(),
        }
    }

    pub fn terms(&self) -> IndexSet<Term> {
        match &self {
            AtomicFormula::Literal(l) => l.atom.terms.iter().cloned().collect(),
            AtomicFormula::Comparison(c) => IndexSet::from([c.lhs.clone(), c.rhs.clone()]),
        }
    }
}

impl TryFrom<mini_gringo_cl::AtomicFormula> for AtomicFormula {
    type Error = &'static str;

    fn try_from(value: mini_gringo_cl::AtomicFormula) -> Result<Self, Self::Error> {
        match value {
            mini_gringo_cl::AtomicFormula::Literal(literal) => {
                let l: Literal = literal.try_into()?;
                Ok(AtomicFormula::Literal(l))
            }
            mini_gringo_cl::AtomicFormula::Comparison(comparison) => {
                let c: Comparison = comparison.try_into()?;
                Ok(AtomicFormula::Comparison(c))
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Head {
    Basic(Atom),
    Choice(Atom),
    Falsity,
}

impl_node!(Head, Format, HeadParser);

impl Head {
    pub fn predicate(&self) -> Option<Predicate> {
        match self {
            Head::Basic(a) => Some(a.predicate()),
            Head::Choice(a) => Some(a.predicate()),
            Head::Falsity => None,
        }
    }

    // TODO: Revisit these helper function; make sure they are symmetric with all the others.

    pub fn terms(&self) -> Option<&[Term]> {
        match self {
            Head::Basic(a) => Some(&a.terms),
            Head::Choice(a) => Some(&a.terms),
            Head::Falsity => None,
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            Head::Basic(a) => a.terms.len(),
            Head::Choice(a) => a.terms.len(),
            Head::Falsity => 0,
        }
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        match &self {
            Head::Basic(a) | Head::Choice(a) => a.variables(),
            Head::Falsity => IndexSet::new(),
        }
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        match &self {
            Head::Basic(a) | Head::Choice(a) => a.function_constants(),
            Head::Falsity => IndexSet::new(),
        }
    }
}

impl TryFrom<mini_gringo_cl::Head> for Head {
    type Error = &'static str;

    fn try_from(value: mini_gringo_cl::Head) -> Result<Self, Self::Error> {
        match value {
            mini_gringo_cl::Head::Basic(atom) => {
                let a: Atom = atom.try_into()?;
                Ok(Head::Basic(a))
            }
            mini_gringo_cl::Head::Choice(atom) => {
                let a: Atom = atom.try_into()?;
                Ok(Head::Choice(a))
            }
            mini_gringo_cl::Head::Falsity => Ok(Head::Falsity),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, IntoIterator)]
pub struct Body {
    #[into_iterator(owned, ref, ref_mut)]
    pub formulas: Vec<AtomicFormula>,
}

impl_node!(Body, Format, BodyParser);

impl Body {
    pub fn predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = IndexSet::new();
        for formula in self.formulas.iter() {
            predicates.extend(formula.predicates())
        }
        predicates
    }

    pub fn positive_predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = IndexSet::new();
        for formula in self.formulas.iter() {
            predicates.extend(formula.positive_predicates())
        }
        predicates
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = IndexSet::new();
        for formula in self.formulas.iter() {
            vars.extend(formula.variables())
        }
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut functions = IndexSet::new();
        for formula in self.formulas.iter() {
            functions.extend(formula.function_constants())
        }
        functions
    }

    pub fn terms(&self) -> IndexSet<Term> {
        let mut terms = IndexSet::new();
        for formula in self.formulas.iter() {
            terms.extend(formula.terms())
        }
        terms
    }
}

impl FromIterator<AtomicFormula> for Body {
    fn from_iter<T: IntoIterator<Item = AtomicFormula>>(iter: T) -> Self {
        Body {
            formulas: iter.into_iter().collect(),
        }
    }
}

impl TryFrom<mini_gringo_cl::Body> for Body {
    type Error = &'static str;

    fn try_from(value: mini_gringo_cl::Body) -> Result<Self, Self::Error> {
        let mut formulas = Vec::new();
        for formula in value.formulas {
            match formula {
                mini_gringo_cl::BodyLiteral::GsixConditionalLiteral(_) => {
                    return Err("Gringo 6 conditional literals may not have empty bodies");
                }
                mini_gringo_cl::BodyLiteral::GfiveConditionalLiteral(conditional_literal) => {
                    let is_basic = conditional_literal.basic();
                    match conditional_literal.head {
                        mini_gringo_cl::ConditionalHead::AtomicFormula(atomic_formula) => {
                            if is_basic {
                                let af: AtomicFormula = atomic_formula.try_into()?;
                                formulas.push(af);
                            } else {
                                return Err(
                                    "mini-gringo programs cannot contain conditional literals",
                                );
                            }
                        }
                        mini_gringo_cl::ConditionalHead::Falsity => {
                            return Err("mini-gringo rule bodies cannot contain #false");
                        }
                    }
                }
            }
        }

        Ok(Body { formulas })
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Rule {
    pub head: Head,
    pub body: Body,
}

impl_node!(Rule, Format, RuleParser);

impl Rule {
    pub fn predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = IndexSet::new();
        if let Some(predicate) = self.head.predicate() {
            predicates.insert(predicate);
        }
        predicates.extend(self.body.predicates());
        predicates
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = self.head.variables();
        vars.extend(self.body.variables());
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut functions = self.head.function_constants();
        functions.extend(self.body.function_constants());
        functions
    }

    pub fn terms(&self) -> IndexSet<Term> {
        let mut terms = IndexSet::new();
        if let Some(head_terms) = self.head.terms() {
            head_terms.iter().for_each(|term| {
                terms.insert(term.clone());
            });
        }
        terms.extend(self.body.terms());
        terms
    }
}

impl TryFrom<mini_gringo_cl::Rule> for Rule {
    type Error = &'static str;

    fn try_from(value: mini_gringo_cl::Rule) -> Result<Self, Self::Error> {
        let head: Head = value.head.try_into()?;
        let body: Body = value.body.try_into()?;
        Ok(Rule { head, body })
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, IntoIterator)]
pub struct Program {
    #[into_iterator(owned, ref, ref_mut)]
    pub rules: Vec<Rule>,
}

impl_node!(Program, Format, ProgramParser);

impl Program {
    pub fn predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = IndexSet::new();
        for rule in &self.rules {
            predicates.extend(rule.predicates())
        }
        predicates
    }

    pub fn head_predicates(&self) -> IndexSet<Predicate> {
        let mut result = IndexSet::new();
        for rule in &self.rules {
            if let Some(predicate) = rule.head.predicate() {
                result.insert(predicate.clone());
            }
        }
        result
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = IndexSet::new();
        for rule in self.rules.iter() {
            vars.extend(rule.variables())
        }
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut functions = IndexSet::new();
        for rule in self.rules.iter() {
            functions.extend(rule.function_constants());
        }
        functions
    }

    pub fn max_arity(&self) -> usize {
        let mut max_arity = 0;
        for rule in self.rules.iter() {
            let head_arity = rule.head.arity();
            if head_arity > max_arity {
                max_arity = head_arity;
            }
        }
        max_arity
    }
}

impl FromIterator<Rule> for Program {
    fn from_iter<T: IntoIterator<Item = Rule>>(iter: T) -> Self {
        Program {
            rules: iter.into_iter().collect(),
        }
    }
}

impl TryFrom<mini_gringo_cl::Program> for Program {
    type Error = &'static str;

    fn try_from(value: mini_gringo_cl::Program) -> Result<Self, Self::Error> {
        let mut rules = Vec::new();
        for rule in value.rules {
            let r = Rule::try_from(rule)?;
            rules.push(r);
        }
        Ok(Program { rules })
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{
            Atom, AtomicFormula, Body, Comparison, Head, PrecomputedTerm, Program, Relation, Rule,
            Term,
        },
        indexmap::IndexSet,
    };

    #[test]
    fn test_program_function_constants() {
        // p :- b != a.
        let program = Program {
            rules: vec![Rule {
                head: Head::Basic(Atom {
                    predicate_symbol: "p".into(),
                    terms: vec![],
                }),
                body: Body {
                    formulas: vec![AtomicFormula::Comparison(Comparison {
                        lhs: Term::PrecomputedTerm(PrecomputedTerm::Symbol("a".into())),
                        rhs: Term::PrecomputedTerm(PrecomputedTerm::Symbol("b".into())),
                        relation: Relation::NotEqual,
                    })],
                },
            }],
        };
        assert_eq!(
            program.function_constants(),
            IndexSet::from(["a".into(), "b".into()])
        )
    }
}
