pub mod gringo;
pub mod mini_gringo;
pub mod mini_gringo_cl;

pub trait Definite {
    fn definite(&self) -> bool;
}

impl Definite for mini_gringo_cl::AtomicFormula {
    fn definite(&self) -> bool {
        match self {
            mini_gringo_cl::AtomicFormula::Literal(literal) => {
                matches!(literal.sign, mini_gringo_cl::Sign::NoSign)
            }
            mini_gringo_cl::AtomicFormula::Comparison(_) => true,
        }
    }
}

// TODO : is 'definite' i.e. absence of negation, appropriate for conditional literals?
impl Definite for mini_gringo_cl::ConditionalLiteral {
    fn definite(&self) -> bool {
        let definite_head = match &self.head {
            mini_gringo_cl::ConditionalHead::AtomicFormula(f) => f.definite(),
            mini_gringo_cl::ConditionalHead::Falsity => false,
        };

        let definite_body = {
            let mut flag = true;
            for f in self.conditions.formulas.iter() {
                if !f.definite() {
                    flag = false;
                }
            }
            flag
        };

        definite_head && definite_body
    }
}

impl Definite for mini_gringo_cl::Rule {
    fn definite(&self) -> bool {
        match self.head {
            mini_gringo_cl::Head::Choice(_) => false,
            mini_gringo_cl::Head::Basic(_) | mini_gringo_cl::Head::Falsity => {
                let mut flag = true;
                for literal in self.body.formulas.iter() {
                    let cl = match literal {
                        mini_gringo_cl::BodyLiteral::GfiveConditionalLiteral(cl) => cl,
                        mini_gringo_cl::BodyLiteral::GsixConditionalLiteral(cl) => cl,
                    };
                    if !cl.definite() {
                        flag = false;
                    }
                }
                flag
            }
        }
    }
}

impl Definite for mini_gringo_cl::Program {
    fn definite(&self) -> bool {
        for rule in self.rules.iter() {
            if !rule.definite() {
                return false;
            }
        }
        true
    }
}

impl Definite for gringo::Program {
    fn definite(&self) -> bool {
        let program: mini_gringo_cl::Program = self.clone().into();
        program.definite()
    }
}

impl Definite for mini_gringo::Program {
    fn definite(&self) -> bool {
        let program: mini_gringo_cl::Program = self.clone().into();
        program.definite()
    }
}

#[cfg(test)]
mod tests {
    use crate::syntax_tree::asp::{Definite, mini_gringo_cl};

    #[test]
    fn test_definite_program() {
        for src in [
            "p :- q. q :- p.",
            "p(X) :- q(X), X < Y.",
            "p(X) :- q(X) : r(X,Y).",
            ":- X = 1..3, nottingham(X). p.",
        ] {
            let program: mini_gringo_cl::Program = src.parse().unwrap();
            assert!(program.definite())
        }

        for src in [
            "p :- q. {q} :- p.",
            "p(X) :- not not q(X), X < Y.",
            "p(X) :- #false : q(X).",
            "p(X) :- X = Y : not q(X).",
            ":- X = 1..3, not ham(X). p.",
        ] {
            let program: mini_gringo_cl::Program = src.parse().unwrap();
            assert!(!program.definite())
        }
    }
}
