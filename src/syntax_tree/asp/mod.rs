pub mod gringo;
pub mod mini_gringo;
pub mod mini_gringo_cl;

pub trait Definite {
    fn definite(&self) -> bool;
}

impl Definite for mini_gringo::AtomicFormula {
    fn definite(&self) -> bool {
        match self {
            mini_gringo::AtomicFormula::Literal(literal) => {
                matches!(literal.sign, mini_gringo::Sign::NoSign)
            }
            mini_gringo::AtomicFormula::Comparison(_) => true,
        }
    }
}

// TODO : is 'definite' i.e. absence of negation, appropriate for conditional literals?
// impl Definite for mini_gringo_cl::ConditionalLiteral {
//     fn definite(&self) -> bool {
//         let definite_head = match &self.head {
//             mini_gringo_cl::ConditionalHead::AtomicFormula(f) => f.definite(),
//             mini_gringo_cl::ConditionalHead::Falsity => false,
//         };

//         let definite_body = {
//             let mut flag = true;
//             for f in self.conditions.formulas.iter() {
//                 if !f.definite() {
//                     flag = false;
//                 }
//             }
//             flag
//         };

//         definite_head && definite_body
//     }
// }

impl Definite for mini_gringo::Rule {
    fn definite(&self) -> bool {
        match self.head {
            mini_gringo::Head::Choice(_) => false,
            mini_gringo::Head::Basic(_) | mini_gringo::Head::Falsity => {
                let mut flag = true;
                for formula in self.body.formulas.iter() {
                    if !formula.definite() {
                        flag = false;
                    }
                }
                flag
            }
        }
    }
}

impl Definite for mini_gringo::Program {
    fn definite(&self) -> bool {
        for rule in self.rules.iter() {
            if !rule.definite() {
                return false;
            }
        }
        true
    }
}

impl Definite for mini_gringo_cl::Program {
    fn definite(&self) -> bool {
        match mini_gringo::Program::try_from(self.clone()) {
            Ok(p) => p.definite(),
            Err(_) => false,
        }
    }
}

impl Definite for gringo::Program {
    fn definite(&self) -> bool {
        let program: mini_gringo_cl::Program = self.clone().into();
        program.definite()
    }
}

#[cfg(test)]
mod tests {
    use crate::syntax_tree::asp::{Definite, gringo};

    #[test]
    fn test_definite_program() {
        for src in [
            "p :- q. q :- p.",
            "p(X) :- q(X), X < Y.",
            ":- X = 1..3, nottingham(X). p.",
        ] {
            let program: gringo::Program = src.parse().unwrap();
            assert!(program.definite())
        }

        for src in [
            "p :- q. {q} :- p.",
            "p(X) :- not not q(X), X < Y.",
            "p(X) :- #false : q(X).",
            "p(X) :- X = Y : not q(X).",
            "p(X) :- q(X) : r(X,Y).",
            ":- X = 1..3, not ham(X). p.",
        ] {
            let program: gringo::Program = src.parse().unwrap();
            assert!(!program.definite())
        }
    }
}
