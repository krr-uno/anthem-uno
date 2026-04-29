use crate::syntax_tree::asp::mini_gringo_cl::{
    AtomicFormula, Body, BodyLiteral, ConditionalHead, ConditionalLiteral, Program, Rule, Term,
};

impl Term {
    pub fn is_precomputed(&self) -> bool {
        matches!(self, Term::PrecomputedTerm(_))
    }

    pub fn contains_arithmetic_operations(&self) -> bool {
        match self {
            Term::PrecomputedTerm(_) | Term::Variable(_) => false,
            Term::UnaryOperation { .. } | Term::BinaryOperation { .. } => true,
        }
    }
}

// Replace first occurrence of an expression H :: L with H : L
fn replace_gsix_conditional_with_gfive_conditional(
    rule: &Rule,
) -> Option<(Rule, ConditionalLiteral)> {
    let mut replaced = None;
    let mut formulas = vec![];
    for b in &rule.body.formulas {
        match b {
            BodyLiteral::GfiveConditionalLiteral(cl) => {
                formulas.push(BodyLiteral::GfiveConditionalLiteral(cl.clone()));
            }
            BodyLiteral::GsixConditionalLiteral(cl) => {
                if replaced.is_some() {
                    formulas.push(BodyLiteral::GsixConditionalLiteral(cl.clone()));
                } else {
                    formulas.push(BodyLiteral::GfiveConditionalLiteral(cl.clone()));
                    replaced = Some(cl.clone());
                }
            }
        }
    }

    replaced.map(|literal| {
        (
            Rule {
                head: rule.head.clone(),
                body: Body { formulas },
            },
            literal,
        )
    })
}

// True if r1 is backwards-compatible with r2 when
// r2 is obtained from r1 by replacing an expression
// H :: L with H : L
fn backwards_compatible(r1: &Rule, r2: &Rule, l: &ConditionalLiteral) -> bool {
    let r1_globals = r1.global_variables();
    let r2_globals = r2.global_variables();

    if r1_globals.difference(&r2_globals).next().is_some()
        || r2_globals.difference(&r1_globals).next().is_some()
    {
        false
    } else {
        match &l.head {
            ConditionalHead::AtomicFormula(formula) => match formula {
                AtomicFormula::Literal(literal) => {
                    let mut arithmetic = false;
                    for term in literal.atom.terms.iter() {
                        if term.contains_arithmetic_operations() {
                            arithmetic = true;
                        }
                    }
                    !arithmetic
                }
                AtomicFormula::Comparison(comparison) => {
                    comparison.lhs.is_precomputed() && comparison.rhs.is_precomputed()
                }
            },
            ConditionalHead::Falsity => true,
        }
    }
}

pub trait BackwardsCompatibility {
    fn is_provably_backwards_compatible(&self) -> bool;
}

impl BackwardsCompatibility for Rule {
    fn is_provably_backwards_compatible(&self) -> bool {
        let mut compatible = true;
        let mut f1 = self.clone();
        let mut f2 = replace_gsix_conditional_with_gfive_conditional(&f1);
        while f2.is_some() {
            let (r, l) = f2.as_ref().unwrap();
            if !backwards_compatible(&f1, r, l) {
                compatible = false;
            }
            f1 = r.clone();
            f2 = replace_gsix_conditional_with_gfive_conditional(&f1);
        }
        compatible
    }
}

impl BackwardsCompatibility for Program {
    fn is_provably_backwards_compatible(&self) -> bool {
        let mut compatible = true;
        for rule in &self.rules {
            if !rule.is_provably_backwards_compatible() {
                compatible = false;
            }
        }
        compatible
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        analyzing::backwards_compatibility::BackwardsCompatibility,
        syntax_tree::asp::mini_gringo_cl::Rule,
    };

    #[test]
    fn test_is_provably_backwards_compatible_rule() {
        for rule in [
            "a :- not a.",
            "a :- #false :: q(X+1), not r(X); b.",
            "a :- b; 1 = 1 :: q(X+1), not r(X).",
            "a :- #false :: q(X+1); p(X) :: q(X).",
            "p :- t :: q.",
        ] {
            let rule: Rule = rule.parse().unwrap();
            assert!(rule.is_provably_backwards_compatible())
        }

        for rule in [
            ":- X = 1..3 :: q(X).",
            "p(X) :- t(X,Y) :: not q(X).",
            "a :- b; 1 = X :: q(X+1), not r(X).",
            "a :- #false :: q(X+1); p(|X|) :: q(X).",
        ] {
            let rule: Rule = rule.parse().unwrap();
            assert!(!rule.is_provably_backwards_compatible())
        }
    }
}
