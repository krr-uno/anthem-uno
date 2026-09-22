use {
    crate::syntax_tree::fol::sigma_0::{self as fol, Sort},
    anyhow::{Context as _, Result},
    std::{fmt, fs::File, io::Write as _, path::Path},
};

pub mod smtlib;
pub mod tptp;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Function {
    pub function_symbol: String,
    pub sort: Sort,
    pub arity: usize,
}

impl From<fol::Function> for Function {
    fn from(value: fol::Function) -> Self {
        Function {
            function_symbol: value.function_symbol,
            sort: value.sort,
            arity: value.terms.len(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum Interpretation {
    Standard,
    Integer,
}

impl fmt::Display for Interpretation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Interpretation::Standard => write!(f, include_str!("standard_interpretation.p")),
            Interpretation::Integer => Ok(()),
        }
    }
}

impl Interpretation {
    pub fn to_file<P: AsRef<Path>>(self, path: P) -> Result<()> {
        let path = path.as_ref();
        let mut file = File::create(path)
            .with_context(|| format!("could not create file `{}`", path.display()))?;
        write!(file, "{self}").with_context(|| format!("could not write file `{}`", path.display()))
    }
}
