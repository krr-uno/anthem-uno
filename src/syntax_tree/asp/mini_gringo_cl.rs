use {
    crate::{
        formatting::asp::mini_gringo_cl::default::Format,
        parsing::asp::mini_gringo_cl::pest::{
            AtomParser, AtomicFormulaParser, BinaryOperatorParser, BodyParser, ComparisonParser,
            ConditionalBodyParser, ConditionalHeadParser, ConditionalLiteralParser, HeadParser,
            LiteralParser, PrecomputedTermParser, PredicateParser, ProgramParser, RelationParser,
            RuleParser, SignParser, TermParser, UnaryOperatorParser, VariableParser,
        },
        syntax_tree::{Node, asp, impl_node},
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

impl From<asp::mini_gringo::PrecomputedTerm> for PrecomputedTerm {
    fn from(value: asp::mini_gringo::PrecomputedTerm) -> Self {
        match value {
            asp::mini_gringo::PrecomputedTerm::Infimum => PrecomputedTerm::Infimum,
            asp::mini_gringo::PrecomputedTerm::Numeral(n) => PrecomputedTerm::Numeral(n),
            asp::mini_gringo::PrecomputedTerm::Symbol(s) => PrecomputedTerm::Symbol(s),
            asp::mini_gringo::PrecomputedTerm::Supremum => PrecomputedTerm::Supremum,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Variable(pub String);

impl_node!(Variable, Format, VariableParser);

impl From<asp::mini_gringo::Variable> for Variable {
    fn from(value: asp::mini_gringo::Variable) -> Self {
        Variable(value.0)
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum UnaryOperator {
    Negative,
    AbsoluteValue,
}

impl_node!(UnaryOperator, Format, UnaryOperatorParser);

impl From<asp::mini_gringo::UnaryOperator> for UnaryOperator {
    fn from(value: asp::mini_gringo::UnaryOperator) -> Self {
        match value {
            asp::mini_gringo::UnaryOperator::Negative => UnaryOperator::Negative,
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum BinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    Interval,
}

impl_node!(BinaryOperator, Format, BinaryOperatorParser);

impl From<asp::mini_gringo::BinaryOperator> for BinaryOperator {
    fn from(value: asp::mini_gringo::BinaryOperator) -> Self {
        match value {
            asp::mini_gringo::BinaryOperator::Add => BinaryOperator::Add,
            asp::mini_gringo::BinaryOperator::Subtract => BinaryOperator::Subtract,
            asp::mini_gringo::BinaryOperator::Multiply => BinaryOperator::Multiply,
            asp::mini_gringo::BinaryOperator::Divide => BinaryOperator::Divide,
            asp::mini_gringo::BinaryOperator::Modulo => BinaryOperator::Modulo,
            asp::mini_gringo::BinaryOperator::Interval => BinaryOperator::Interval,
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

impl From<asp::mini_gringo::Term> for Term {
    fn from(value: asp::mini_gringo::Term) -> Self {
        match value {
            asp::mini_gringo::Term::PrecomputedTerm(t) => Term::PrecomputedTerm(t.into()),
            asp::mini_gringo::Term::Variable(v) => Term::Variable(v.into()),
            asp::mini_gringo::Term::UnaryOperation { op, arg } => {
                let term = Term::from(*arg);
                Term::UnaryOperation {
                    op: op.into(),
                    arg: term.into(),
                }
            }
            asp::mini_gringo::Term::BinaryOperation { op, lhs, rhs } => {
                let left = Term::from(*lhs);
                let right = Term::from(*rhs);
                Term::BinaryOperation {
                    op: op.into(),
                    lhs: left.into(),
                    rhs: right.into(),
                }
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

impl From<asp::mini_gringo::Atom> for Atom {
    fn from(value: asp::mini_gringo::Atom) -> Self {
        let terms: Vec<Term> = value.terms.into_iter().map(Term::from).collect();
        Atom {
            predicate_symbol: value.predicate_symbol,
            terms,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Sign {
    NoSign,
    Negation,
    DoubleNegation,
}

impl_node!(Sign, Format, SignParser);

impl From<asp::mini_gringo::Sign> for Sign {
    fn from(value: asp::mini_gringo::Sign) -> Self {
        match value {
            asp::mini_gringo::Sign::NoSign => Sign::NoSign,
            asp::mini_gringo::Sign::Negation => Sign::Negation,
            asp::mini_gringo::Sign::DoubleNegation => Sign::DoubleNegation,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Literal {
    pub sign: Sign,
    pub atom: Atom,
}

impl_node!(Literal, Format, LiteralParser);

impl From<asp::mini_gringo::Literal> for Literal {
    fn from(value: asp::mini_gringo::Literal) -> Self {
        Literal {
            sign: value.sign.into(),
            atom: value.atom.into(),
        }
    }
}

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

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Relation {
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

impl_node!(Relation, Format, RelationParser);

impl From<asp::mini_gringo::Relation> for Relation {
    fn from(value: asp::mini_gringo::Relation) -> Self {
        match value {
            asp::mini_gringo::Relation::Equal => Relation::Equal,
            asp::mini_gringo::Relation::NotEqual => Relation::NotEqual,
            asp::mini_gringo::Relation::Less => Relation::Less,
            asp::mini_gringo::Relation::LessEqual => Relation::LessEqual,
            asp::mini_gringo::Relation::Greater => Relation::Greater,
            asp::mini_gringo::Relation::GreaterEqual => Relation::GreaterEqual,
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

impl From<asp::mini_gringo::Comparison> for Comparison {
    fn from(value: asp::mini_gringo::Comparison) -> Self {
        Comparison {
            relation: value.relation.into(),
            lhs: value.lhs.into(),
            rhs: value.rhs.into(),
        }
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
}

impl From<asp::mini_gringo::AtomicFormula> for AtomicFormula {
    fn from(value: asp::mini_gringo::AtomicFormula) -> Self {
        match value {
            asp::mini_gringo::AtomicFormula::Literal(l) => AtomicFormula::Literal(l.into()),
            asp::mini_gringo::AtomicFormula::Comparison(c) => AtomicFormula::Comparison(c.into()),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum ConditionalHead {
    AtomicFormula(AtomicFormula),
    Falsity,
}

impl_node!(ConditionalHead, Format, ConditionalHeadParser);

impl ConditionalHead {
    pub fn variables(&self) -> IndexSet<Variable> {
        match &self {
            ConditionalHead::AtomicFormula(a) => a.variables(),
            ConditionalHead::Falsity => IndexSet::new(),
        }
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        match &self {
            ConditionalHead::AtomicFormula(a) => a.function_constants(),
            ConditionalHead::Falsity => IndexSet::new(),
        }
    }

    pub fn predicates(&self) -> IndexSet<Predicate> {
        match &self {
            ConditionalHead::AtomicFormula(a) => a.predicates(),
            ConditionalHead::Falsity => IndexSet::new(),
        }
    }

    pub fn positive_predicates(&self) -> IndexSet<Predicate> {
        match &self {
            ConditionalHead::AtomicFormula(a) => a.positive_predicates(),
            ConditionalHead::Falsity => IndexSet::new(),
        }
    }
}

impl From<asp::mini_gringo::AtomicFormula> for ConditionalHead {
    fn from(value: asp::mini_gringo::AtomicFormula) -> Self {
        ConditionalHead::AtomicFormula(value.into())
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct ConditionalBody {
    pub formulas: Vec<AtomicFormula>,
}

impl_node!(ConditionalBody, Format, ConditionalBodyParser);

impl ConditionalBody {
    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = IndexSet::new();
        for f in self.formulas.iter() {
            vars.extend(f.variables());
        }
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut constants = IndexSet::new();
        for f in self.formulas.iter() {
            constants.extend(f.function_constants());
        }
        constants
    }

    pub fn predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = IndexSet::new();
        for f in self.formulas.iter() {
            predicates.extend(f.predicates());
        }
        predicates
    }

    pub fn positive_predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = IndexSet::new();
        for f in self.formulas.iter() {
            predicates.extend(f.positive_predicates());
        }
        predicates
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct ConditionalLiteral {
    pub head: ConditionalHead,
    pub conditions: ConditionalBody,
}

impl_node!(ConditionalLiteral, Format, ConditionalLiteralParser);

impl From<asp::mini_gringo::AtomicFormula> for ConditionalLiteral {
    fn from(value: asp::mini_gringo::AtomicFormula) -> Self {
        ConditionalLiteral {
            head: value.into(),
            conditions: ConditionalBody { formulas: vec![] },
        }
    }
}

impl ConditionalLiteral {
    pub fn basic(&self) -> bool {
        self.conditions.formulas.is_empty()
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = self.head.variables();
        vars.extend(self.conditions.variables());
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut constants = self.head.function_constants();
        constants.extend(self.conditions.function_constants());
        constants
    }

    pub fn global_variables(&self) -> IndexSet<Variable> {
        let mut head_vars = self.head.variables();
        let body_vars = self.conditions.variables();
        head_vars.retain(|v| !body_vars.contains(v));
        head_vars
    }

    pub fn predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = self.head.predicates();
        predicates.extend(self.conditions.predicates());
        predicates
    }

    pub fn positive_predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = self.head.positive_predicates();
        predicates.extend(self.conditions.positive_predicates());
        predicates
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

impl From<asp::mini_gringo::Head> for Head {
    fn from(value: asp::mini_gringo::Head) -> Self {
        match value {
            asp::mini_gringo::Head::Basic(atom) => Head::Basic(atom.into()),
            asp::mini_gringo::Head::Choice(atom) => Head::Choice(atom.into()),
            asp::mini_gringo::Head::Falsity => Head::Falsity,
        }
    }
}

#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BodyLiteral {
    ConditionalLiteral(ConditionalLiteral),
}

impl BodyLiteral {
    pub fn predicates(&self) -> IndexSet<Predicate> {
        match self {
            BodyLiteral::ConditionalLiteral(l) => l.predicates(),
        }
    }

    pub fn positive_predicates(&self) -> IndexSet<Predicate> {
        match self {
            BodyLiteral::ConditionalLiteral(l) => l.positive_predicates(),
        }
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        match self {
            BodyLiteral::ConditionalLiteral(l) => l.variables(),
        }
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        match self {
            BodyLiteral::ConditionalLiteral(l) => l.function_constants(),
        }
    }

    pub fn global_variables(&self) -> IndexSet<Variable> {
        match self {
            BodyLiteral::ConditionalLiteral(l) => l.global_variables(),
        }
    }
}

impl From<asp::mini_gringo::AtomicFormula> for BodyLiteral {
    fn from(value: asp::mini_gringo::AtomicFormula) -> Self {
        BodyLiteral::ConditionalLiteral(value.into())
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, IntoIterator)]
pub struct Body {
    #[into_iterator(owned, ref, ref_mut)]
    pub formulas: Vec<BodyLiteral>,
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
}

impl FromIterator<BodyLiteral> for Body {
    fn from_iter<T: IntoIterator<Item = BodyLiteral>>(iter: T) -> Self {
        Body {
            formulas: iter.into_iter().collect(),
        }
    }
}

impl From<asp::mini_gringo::Body> for Body {
    fn from(value: asp::mini_gringo::Body) -> Self {
        Body::from_iter(value.into_iter().map(BodyLiteral::from))
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

    pub fn global_variables(&self) -> IndexSet<Variable> {
        let mut vars = self.head.variables();
        for formula in self.body.formulas.iter() {
            vars.extend(formula.global_variables());
        }
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut functions = self.head.function_constants();
        functions.extend(self.body.function_constants());
        functions
    }

    pub fn is_choice_rule(&self) -> bool {
        matches!(self.head, Head::Choice(_))
    }
}

impl From<asp::mini_gringo::Rule> for Rule {
    fn from(value: asp::mini_gringo::Rule) -> Self {
        Rule {
            head: value.head.into(),
            body: value.body.into(),
        }
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
}

impl FromIterator<Rule> for Program {
    fn from_iter<T: IntoIterator<Item = Rule>>(iter: T) -> Self {
        Program {
            rules: iter.into_iter().collect(),
        }
    }
}

impl From<asp::mini_gringo::Program> for Program {
    fn from(value: asp::mini_gringo::Program) -> Self {
        Program::from_iter(value.into_iter().map(Rule::from))
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{
            Atom, AtomicFormula, Body, Comparison, Head, PrecomputedTerm, Program, Relation, Rule,
            Term,
        },
        crate::syntax_tree::asp::{
            mini_gringo,
            mini_gringo_cl::{
                self, BodyLiteral, ConditionalBody, ConditionalHead, ConditionalLiteral,
            },
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
                    formulas: vec![BodyLiteral::ConditionalLiteral(ConditionalLiteral {
                        head: ConditionalHead::AtomicFormula(AtomicFormula::Comparison(
                            Comparison {
                                lhs: Term::PrecomputedTerm(PrecomputedTerm::Symbol("a".into())),
                                rhs: Term::PrecomputedTerm(PrecomputedTerm::Symbol("b".into())),
                                relation: Relation::NotEqual,
                            },
                        )),
                        conditions: ConditionalBody { formulas: vec![] },
                    })],
                },
            }],
        };
        assert_eq!(
            program.function_constants(),
            IndexSet::from(["a".into(), "b".into()])
        )
    }

    #[test]
    fn test_mini_gringo_identity() {
        for src in ["p :- q. q :- p."] {
            let mg: mini_gringo::Program = src.parse().unwrap();
            let left = mini_gringo_cl::Program::from(mg);
            let right: mini_gringo_cl::Program = src.parse().unwrap();
            assert_eq!(left, right, "left != right:\n{left}\n!=\n{right}")
        }
    }
}
