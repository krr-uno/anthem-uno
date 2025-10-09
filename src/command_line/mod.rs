pub mod arguments;
pub mod files;
pub mod procedures;

pub(crate) enum Program {
    MiniGringo(crate::syntax_tree::asp::mini_gringo::Program),
    MiniGringoCl(crate::syntax_tree::asp::mini_gringo_cl::Program),
}
