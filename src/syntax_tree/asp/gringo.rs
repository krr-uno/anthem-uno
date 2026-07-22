use {
    crate::{
        formatting::asp::gringo::default::Format,
        parsing::asp::gringo::pest::{
            AtomParser, AtomicFormulaParser, BinaryOperatorParser, BodyLiteralParser, BodyParser,
            ComparisonParser, ConditionalBodyParser, ConditionalHeadParser, HeadParser,
            LiteralParser, PrecomputedTermParser, PredicateParser, ProgramParser, RelationParser,
            RuleParser, SignParser, TermParser, UnaryOperatorParser, VariableParser,
        },
        syntax_tree::{Node, asp, impl_node},
    },
    derive_more::derive::IntoIterator,
    indexmap::IndexSet,
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BasicSymbol {
    Infimum,
    Numeral(isize),
    Symbol(String),
    Supremum,
}

impl BasicSymbol {
    pub fn function_constants(&self) -> IndexSet<String> {
        match &self {
            BasicSymbol::Infimum => IndexSet::new(),
            BasicSymbol::Numeral(_) => IndexSet::new(),
            BasicSymbol::Symbol(s) => IndexSet::from([s.clone()]),
            BasicSymbol::Supremum => IndexSet::new(),
        }
    }
}

impl_node!(BasicSymbol, Format, PrecomputedTermParser);

// Potassco User Guide, Anonymous Variables:
// Unlike a variable name whose recurrences within a rule refer to the same variable,
// the token ‘_’ (not followed by any letter) stands for an anonymous variable that does not recur anywhere.
// (One can view this as if a new variable name is invented on each occurrence of ‘_’.)
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Variable {
    pub name: Option<String>,
}

impl_node!(Variable, Format, VariableParser);

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum UnaryOperator {
    Negative,
    AbsoluteValue,
}

impl_node!(UnaryOperator, Format, UnaryOperatorParser);

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

impl From<asp::mini_gringo::BinaryOperator> for BinaryOperator {
    fn from(value: asp::mini_gringo::BinaryOperator) -> Self {
        match value {
            asp::mini_gringo::BinaryOperator::Add => BinaryOperator::Add,
            asp::mini_gringo::BinaryOperator::Subtract => BinaryOperator::Subtract,
            asp::mini_gringo::BinaryOperator::Multiply => BinaryOperator::Multiply,
            asp::mini_gringo::BinaryOperator::Divide => BinaryOperator::Divide,
            asp::mini_gringo::BinaryOperator::DivideInteger => BinaryOperator::DivideInteger,
            asp::mini_gringo::BinaryOperator::Modulo => BinaryOperator::Modulo,
            asp::mini_gringo::BinaryOperator::ModuloInteger => BinaryOperator::ModuloInteger,
            asp::mini_gringo::BinaryOperator::Interval => BinaryOperator::Interval,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Term {
    PrecomputedTerm(BasicSymbol),
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

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Predicate {
    pub symbol: String,
    pub arity: usize,
}

impl_node!(Predicate, Format, PredicateParser);

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

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Sign {
    NoSign,
    Negation,
    DoubleNegation,
}

impl_node!(Sign, Format, SignParser);

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

#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BodyLiteral {
    /// Corresponds to a Gringo 5 Conditional Literal
    GfiveConditionalLiteral(ConditionalLiteral),
    /// Corresponds to a Gringo 6 Conditional Literal
    GsixConditionalLiteral(ConditionalLiteral),
}

impl_node!(BodyLiteral, Format, BodyLiteralParser);

impl BodyLiteral {
    pub fn predicates(&self) -> IndexSet<Predicate> {
        match self {
            BodyLiteral::GfiveConditionalLiteral(l) | BodyLiteral::GsixConditionalLiteral(l) => {
                l.predicates()
            }
        }
    }

    pub fn positive_predicates(&self) -> IndexSet<Predicate> {
        match self {
            BodyLiteral::GfiveConditionalLiteral(l) => l.positive_predicates(),
            BodyLiteral::GsixConditionalLiteral(_) => todo!("what are positive_predicates?"),
        }
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        match self {
            BodyLiteral::GfiveConditionalLiteral(l) | BodyLiteral::GsixConditionalLiteral(l) => {
                l.variables()
            }
        }
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        match self {
            BodyLiteral::GfiveConditionalLiteral(l) | BodyLiteral::GsixConditionalLiteral(l) => {
                l.function_constants()
            }
        }
    }

    pub fn global_variables(&self) -> IndexSet<Variable> {
        match self {
            BodyLiteral::GfiveConditionalLiteral(l) => l.global_variables(),
            BodyLiteral::GsixConditionalLiteral(_) => IndexSet::new(),
        }
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

    pub fn named_variables(&self) -> IndexSet<Variable> {
        let mut vars = self.variables();
        vars.retain(|v| v.name.is_some());
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
