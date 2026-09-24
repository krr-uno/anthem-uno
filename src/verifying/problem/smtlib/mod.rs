use {
    super::{Function, Interpretation},
    crate::{
        formatting::fol::sigma_0::smtlib,
        syntax_tree::fol::sigma_0::{
            self as fol, Formula, FunctionConstant, Predicate, Theory,
        },
    },
    anyhow::{Context as _, Result},
    indexmap::IndexSet,
    itertools::Itertools,
    std::{fmt, fs::File, io::Write as _, path::Path},
};

//
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Logic {
    Ufnia,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Role {
    Assertion,
}

impl fmt::Display for Role {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Role::Assertion => write!(f, "assert"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct AnnotatedFormula {
    pub name: String,
    pub role: Role,
    pub formula: Formula,
}

impl AnnotatedFormula {
    pub fn predicates(&self) -> IndexSet<Predicate> {
        self.formula.predicates()
    }

    pub fn symbols(&self) -> IndexSet<String> {
        self.formula.symbols()
    }

    pub fn function_constants(&self) -> IndexSet<FunctionConstant> {
        self.formula.function_constants()
    }

    pub fn functions(&self) -> IndexSet<fol::Function> {
        self.formula.functions()
    }

    pub fn rename_conflicting_symbols(self, possible_conflicts: &IndexSet<Predicate>) -> Self {
        AnnotatedFormula {
            role: self.role,
            formula: self.formula.rename_conflicting_symbols(possible_conflicts),
            name: self.name,
        }
    }
}

impl fmt::Display for AnnotatedFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = &self.name;
        let role = &self.role;
        let formula = crate::formatting::fol::sigma_0::smtlib::Format(&self.formula);
        writeln!(f, "({role} ({formula} :named {name}))")
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Problem {
    pub name: String,
    pub logic: Logic,
    pub interpretation: Interpretation,
    pub formulas: Vec<AnnotatedFormula>,
}

impl Problem {
    pub fn with_name<S: Into<String>>(name: S, logic: Logic) -> Problem {
        Problem {
            name: name.into(),
            interpretation: Interpretation::Integer,
            formulas: vec![],
            logic,
        }
    }

    pub fn add_annotated_formulas(
        mut self,
        annotated_formulas: impl IntoIterator<Item = AnnotatedFormula>,
    ) -> Self {
        for anf in annotated_formulas {
            if anf.name.is_empty() {
                self.formulas.push(AnnotatedFormula {
                    name: "unnamed_formula".to_string(),
                    role: anf.role,
                    formula: anf.formula,
                });
            } else if anf.name.starts_with('_') {
                self.formulas.push(AnnotatedFormula {
                    name: format!("f{}", anf.name),
                    role: anf.role,
                    formula: anf.formula,
                });
            } else {
                self.formulas.push(anf);
            }
        }
        self
    }

    pub fn add_theory<F>(mut self, theory: Theory, mut annotate: F) -> Self
    where
        F: FnMut(usize, Formula) -> AnnotatedFormula,
    {
        for (i, formula) in theory.formulas.into_iter().enumerate() {
            self.formulas.push(annotate(i, formula))
        }
        self
    }

    pub fn rename_conflicting_symbols(mut self) -> Self {
        let propositional_predicates =
            IndexSet::from_iter(self.predicates().into_iter().filter(|p| p.arity == 0));

        let formulas = self
            .formulas
            .into_iter()
            .map(|f| f.rename_conflicting_symbols(&propositional_predicates))
            .collect();
        self.formulas = formulas;
        self
    }

    // TODO: Improve naming scheme for formulas
    pub fn create_unique_formula_names(mut self) -> Self {
        let mut formulas = vec![];
        for (i, f) in self.formulas.into_iter().enumerate() {
            formulas.push(AnnotatedFormula {
                name: format!("formula_{i}_{}", f.name),
                role: f.role,
                formula: f.formula,
            });
        }
        self.formulas = formulas;
        self
    }

    pub fn assertions(&self) -> Vec<AnnotatedFormula> {
        self.formulas
            .iter()
            .filter(|f| f.role == Role::Assertion)
            .cloned()
            .collect_vec()
    }

    pub fn predicates(&self) -> IndexSet<Predicate> {
        let mut result = IndexSet::new();
        for formula in &self.formulas {
            result.extend(formula.predicates())
        }
        result
    }

    pub fn symbols(&self) -> IndexSet<String> {
        let mut result = IndexSet::new();
        for formula in &self.formulas {
            result.extend(formula.symbols())
        }
        result
    }

    pub fn function_constants(&self) -> IndexSet<FunctionConstant> {
        let mut result = IndexSet::new();
        for formula in &self.formulas {
            result.extend(formula.function_constants())
        }
        result
    }

    pub fn functions(&self) -> IndexSet<Function> {
        let mut result = IndexSet::new();
        for formula in &self.formulas {
            result.extend(formula.functions().into_iter().map(|f| f.into()))
        }
        result
    }

    pub fn to_file<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        let path = path.as_ref();
        let mut file = File::create(path)
            .with_context(|| format!("could not create file `{}`", path.display()))?;
        write!(file, "{self}").with_context(|| format!("could not write file `{}`", path.display()))
    }
}

impl fmt::Display for Problem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Set logic
        match self.logic {
            Logic::Ufnia => write!(f, "(set-logic UF_NIA)")?,
        }

        // Declare predicates
        for predicate in self.predicates().iter() {
            writeln!(f, "(declare-fun {} Bool)", smtlib::Format(predicate))?;
        }

        // Declare functions
        for function in self.function_constants().iter() {
            writeln!(f, "(declare-fun {} () Int)", smtlib::Format(function))?;
        }
        for function in self.functions().iter() {
            let symbol = &function.function_symbol;
            write!(f, "(declare-fun {symbol} (")?;
            for _i in 1..function.arity {
                write!(f, " Int")?;
            }
            write!(f, " Int)\n")?;
        }

        // Write assertions
        for formula in self.formulas.iter() {
            writeln!(f, "{formula}")?;
        }

        // Set filename
        writeln!(f, "(set-info :filename {})", self.name)?;

        writeln!(f, "(check-sat)")?;

        Ok(())
    }
}
