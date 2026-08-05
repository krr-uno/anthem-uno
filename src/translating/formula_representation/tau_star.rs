use crate::{
    command_line::arguments::Dialect,
    convenience::variable_selection::VariableSelection,
    syntax_tree::{
        asp::{mini_gringo as asp, mini_gringo_cl},
        fol::sigma_0 as fol,
    },
    translating,
};

/// Choose fresh variants of `Vn` by incrementing `n`
pub(crate) fn choose_fresh_global_variables(program: &asp::Program) -> Vec<String> {
    let max_arity = program.max_arity();
    program.choose_fresh_variables("V", max_arity)
}

// Translate a rule using a pre-defined list of global variables
pub(crate) fn tau_star_rule(r: asp::Rule, globals: &[String], dialect: Dialect) -> fol::Formula {
    let rule = mini_gringo_cl::Rule::from(r);
    translating::formula_representation::tau_star_cl::tau_star_rule(rule, globals, dialect)
}

pub trait TauStar {
    type Output;

    fn tau_star(self, dialect: Dialect) -> Self::Output;
}

impl TauStar for asp::Program {
    type Output = fol::Theory;

    fn tau_star(self, dialect: Dialect) -> Self::Output {
        let program = mini_gringo_cl::Program::from(self);
        program.tau_star(dialect)
    }
}
