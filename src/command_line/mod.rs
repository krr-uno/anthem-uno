use crate::{
    syntax_tree::{
        asp::{mini_gringo, mini_gringo_cl},
        fol::sigma_0 as fol,
    },
    translating::formula_representation::tau_star::TauStar,
};

pub mod arguments;
pub mod files;
pub mod procedures;

pub(crate) enum Program {
    MiniGringo(mini_gringo::Program),
    MiniGringoCl(mini_gringo_cl::Program),
}

impl TauStar for Program {
    type Output = fol::Theory;

    fn tau_star(self, dialect: fol::Dialect) -> Self::Output {
        match self {
            Program::MiniGringo(program) => program.tau_star(dialect),
            Program::MiniGringoCl(program) => program.tau_star(dialect),
        }
    }
}
