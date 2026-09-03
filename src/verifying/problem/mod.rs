use {
    crate::{
        command_line::arguments::Decomposition,
        convenience::variable_selection::VariableSelection,
        syntax_tree::fol::sigma_0::{
            self as fol, Formula, FunctionConstant, GeneralTerm, Guard, Predicate, Quantification,
            Quantifier, Sort, SymbolicTerm, Theory,
        },
    },
    anyhow::{Context as _, Result},
    indexmap::IndexSet,
    itertools::Itertools,
    std::{
        fmt,
        fs::File,
        io::Write as _,
        iter::repeat_n,
        path::{Path, PathBuf},
    },
};

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

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Interpretation {
    Standard,
}

impl fmt::Display for Interpretation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Interpretation::Standard => write!(f, include_str!("standard_interpretation.p")),
        }
    }
}

impl Interpretation {
    pub fn to_file<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        let path = path.as_ref();
        let mut file = File::create(path)
            .with_context(|| format!("could not create file `{}`", path.display()))?;
        write!(file, "{self}").with_context(|| format!("could not write file `{}`", path.display()))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Role {
    Axiom,
    Conjecture,
}

impl fmt::Display for Role {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Role::Axiom => write!(f, "axiom"),
            Role::Conjecture => write!(f, "conjecture"),
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
            name: self.name,
            role: self.role,
            formula: self.formula.rename_conflicting_symbols(possible_conflicts),
        }
    }
}

impl fmt::Display for AnnotatedFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = &self.name;
        let role = &self.role;
        let formula = crate::formatting::fol::sigma_0::tptp::Format(&self.formula);
        writeln!(f, "tff({name}, {role}, {formula}).")
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Problem {
    pub name: String,
    pub interpretation: Interpretation,
    pub formulas: Vec<AnnotatedFormula>,
    // Where to find the TPTP file encoding the Interpretation's background theory for use with an 'include' directive
    // If None, the background theory is printed directly when the Problem is formatted
    pub preamble: Option<PathBuf>,
}

impl Problem {
    pub fn with_name<S: Into<String>>(name: S) -> Problem {
        Problem {
            name: name.into(),
            interpretation: Interpretation::Standard,
            formulas: vec![],
            preamble: None,
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

    pub fn function_ordering_axioms(&self, max_symbol: String) -> Vec<Formula> {
        let mut axioms = Vec::new();

        let mut functions = Vec::from_iter(self.functions());
        functions.sort_by_key(|f| f.arity);

        // forall X (a < f(X))
        if let Some(f) = functions.first() {
            let vars = IndexSet::<String>::new().choose_fresh_variables("X", f.arity);
            let axiom = Formula::QuantifiedFormula {
                quantification: Quantification {
                    quantifier: Quantifier::Forall,
                    variables: vars
                        .clone()
                        .into_iter()
                        .map(|v| fol::Variable {
                            name: v,
                            sort: Sort::General,
                        })
                        .collect(),
                },
                formula: Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                    term: GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol(max_symbol)),
                    guards: vec![Guard {
                        relation: fol::Relation::Less,
                        term: GeneralTerm::Function(fol::Function {
                            function_symbol: f.function_symbol.clone(),
                            sort: f.sort,
                            terms: vars.into_iter().map(GeneralTerm::Variable).collect(),
                        }),
                    }],
                }))
                .into(),
            };
            axioms.push(axiom);
        }

        // forall X Y ( f(X) < g(Y) )
        for functions in functions.windows(2) {
            let f = functions[0].clone();
            let g = functions[1].clone();

            let xvars = IndexSet::<String>::new().choose_fresh_variables("X", f.arity);
            let yvars = IndexSet::<String>::new().choose_fresh_variables("Y", g.arity);
            let mut variables: Vec<fol::Variable> = xvars
                .iter()
                .map(|v| fol::Variable {
                    name: v.clone(),
                    sort: Sort::General,
                })
                .collect();
            for y in yvars.iter() {
                variables.push(fol::Variable {
                    name: y.clone(),
                    sort: Sort::General,
                });
            }

            axioms.push(Formula::QuantifiedFormula {
                quantification: Quantification {
                    quantifier: Quantifier::Forall,
                    variables,
                },
                formula: Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                    term: GeneralTerm::Function(fol::Function {
                        function_symbol: f.function_symbol,
                        sort: f.sort,
                        terms: xvars.into_iter().map(GeneralTerm::Variable).collect(),
                    }),
                    guards: vec![Guard {
                        relation: fol::Relation::Less,
                        term: GeneralTerm::Function(fol::Function {
                            function_symbol: g.function_symbol,
                            sort: g.sort,
                            terms: yvars.into_iter().map(GeneralTerm::Variable).collect(),
                        }),
                    }],
                }))
                .into(),
            });
        }

        for f in functions {
            // forall X1 X2 Y1 Y2 ( X1 < Y1 -> f(X1,X2) < f(Y1,Y2) )
            // forall X1 X2 Y1 Y1 ( X1 = Y1 & X2 < Y2 -> f(X1,X2) < f(Y1,Y2) )
            let xvars = IndexSet::<String>::new().choose_fresh_variables("X", f.arity);
            let yvars = IndexSet::<String>::new().choose_fresh_variables("Y", f.arity);

            // f(X1,X2)
            let fx = GeneralTerm::Function(fol::Function {
                function_symbol: f.function_symbol.clone(),
                sort: f.sort,
                terms: xvars
                    .clone()
                    .into_iter()
                    .map(GeneralTerm::Variable)
                    .collect(),
            });
            // f(Y1,Y2)
            let fy = GeneralTerm::Function(fol::Function {
                function_symbol: f.function_symbol.clone(),
                sort: f.sort,
                terms: yvars
                    .clone()
                    .into_iter()
                    .map(GeneralTerm::Variable)
                    .collect(),
            });

            let mut equalities = Vec::new();
            for i in 0..f.arity {
                let x_less_y =
                    Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                        term: GeneralTerm::Variable(xvars[i].clone()),
                        guards: vec![Guard {
                            relation: fol::Relation::Less,
                            term: GeneralTerm::Variable(yvars[i].clone()),
                        }],
                    }));

                let mut antecedent = equalities.clone();
                antecedent.push(x_less_y);

                let less_axiom_i = Formula::BinaryFormula {
                    connective: fol::BinaryConnective::Implication,
                    lhs: Formula::conjoin(antecedent).into(),
                    rhs: Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                        term: fx.clone(),
                        guards: vec![Guard {
                            relation: fol::Relation::Less,
                            term: fy.clone(),
                        }],
                    }))
                    .into(),
                };
                axioms.push(less_axiom_i.universal_closure());

                equalities.push(Formula::AtomicFormula(fol::AtomicFormula::Comparison(
                    fol::Comparison {
                        term: GeneralTerm::Variable(xvars[i].clone()),
                        guards: vec![Guard {
                            relation: fol::Relation::Equal,
                            term: GeneralTerm::Variable(yvars[i].clone()),
                        }],
                    },
                )));
            }

            // forall X1 X2 Y1 Y2 ( X1 = Y1 & X2 = Y2 <-> f(X1,X2) = f(Y1,Y2) )
            let equality_axiom_i = Formula::BinaryFormula {
                connective: fol::BinaryConnective::Equivalence,
                lhs: Formula::conjoin(equalities).into(),
                rhs: Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                    term: fx,
                    guards: vec![Guard {
                        relation: fol::Relation::Equal,
                        term: fy,
                    }],
                }))
                .into(),
            };
            axioms.push(equality_axiom_i.universal_closure());
        }

        axioms
    }

    pub fn axioms(&self) -> Vec<AnnotatedFormula> {
        self.formulas
            .iter()
            .filter(|f| f.role == Role::Axiom)
            .cloned()
            .collect_vec()
    }

    pub fn conjectures(&self) -> Vec<AnnotatedFormula> {
        self.formulas
            .iter()
            .filter(|f| f.role == Role::Conjecture)
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

    pub fn decompose(&self, strategy: Decomposition) -> Vec<Self> {
        match strategy {
            Decomposition::Independent => self.decompose_independent(),
            Decomposition::Sequential => self.decompose_sequential(),
        }
    }

    pub fn decompose_independent(&self) -> Vec<Self> {
        let axioms = self.axioms();
        self.conjectures()
            .into_iter()
            .enumerate()
            .map(|(i, c)| {
                let mut formulas = axioms.clone();
                formulas.push(c);
                Problem {
                    name: format!("{}_{i}", self.name),
                    interpretation: self.interpretation.clone(),
                    formulas,
                    preamble: self.preamble.clone(),
                }
            })
            .collect_vec()
    }

    pub fn decompose_sequential(&self) -> Vec<Self> {
        let mut formulas = self.axioms();
        self.conjectures()
            .into_iter()
            .enumerate()
            .map(|(i, c)| {
                if let Some(last) = formulas.last_mut() {
                    last.role = Role::Axiom;
                }

                formulas.push(c);

                Problem {
                    name: format!("{}_{i}", self.name),
                    interpretation: self.interpretation.clone(),
                    formulas: formulas.clone(),
                    preamble: self.preamble.clone(),
                }
            })
            .collect_vec()
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
        // Preamble
        match &self.preamble {
            Some(path) => writeln!(f, "include('{}').", path.display())?,
            None => write!(f, "{}", self.interpretation)?,
        }

        // Type declarations for predicates
        for (i, predicate) in self.predicates().into_iter().enumerate() {
            let symbol = predicate.symbol;
            let input: String =
                Itertools::intersperse(repeat_n("general", predicate.arity), " * ").collect();
            if predicate.arity > 0 {
                if predicate.arity == 1 {
                    writeln!(f, "tff(predicate_{i}, type, {symbol}: {input} > $o).")?
                } else {
                    writeln!(f, "tff(predicate_{i}, type, {symbol}: ({input}) > $o).")?
                }
            } else {
                writeln!(f, "tff(predicate_{i}, type, {symbol}: $o).")?
            }
        }

        // Type declarations for symbolic constants
        let mut max_symbol = String::from("a");
        for (i, symbol) in self.symbols().into_iter().enumerate() {
            max_symbol = symbol.clone();
            writeln!(f, "tff(type_symbol_{i}, type, {symbol}: symbol).")?
        }

        // Type declarations for function constants
        for (i, constant) in self.function_constants().into_iter().enumerate() {
            let name = crate::formatting::fol::sigma_0::tptp::Format(&constant);
            let sort = match constant.sort {
                Sort::General => "general",
                Sort::Integer => "$int",
                Sort::Symbol => "symbol",
            };
            writeln!(f, "tff(type_function_constant_{i}, type, {name}: {sort}).")?
        }

        // Type declarations for functions
        for (i, function) in self.functions().into_iter().enumerate() {
            let name = function.function_symbol;
            let arity = function.arity;
            let sort = match function.sort {
                Sort::General => "general",
                Sort::Integer => "$int",
                Sort::Symbol => "symbol",
            };

            let input: String = Itertools::intersperse(repeat_n("general", arity), " * ").collect();

            if arity == 1 {
                writeln!(f, "tff(function_{i}, type, {name}: {input} > {sort}).")?
            } else {
                writeln!(f, "tff(function_{i}, type, {name}: ({input}) > {sort}).")?
            }
        }

        // Ordering symbolic constants:
        // a < b < c ...
        let mut symbols = Vec::from_iter(self.symbols());
        symbols.sort_unstable();
        for (i, s) in symbols.windows(2).enumerate() {
            writeln!(
                f,
                "tff(symbol_order_{i}, axiom, p__less__(f__symbolic__({}), f__symbolic__({}))).",
                s[0], s[1]
            )?
        }

        // Ordering symbolic constructor functions:
        // forall X (a < f(X))
        // forall X Y ( X < Y -> f(X) < f(Y) )
        // forall X Y ( X = Y <-> f(X) = f(Y) )
        // etc.
        for (i, axiom) in self.function_ordering_axioms(max_symbol).iter().enumerate() {
            let formatted_axiom = crate::formatting::fol::sigma_0::tptp::Format(axiom);
            writeln!(f, "tff(function_order_{i}, axiom, {formatted_axiom}).")?
        }

        for formula in &self.formulas {
            formula.fmt(f)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{AnnotatedFormula, Interpretation, Problem, Role},
        crate::syntax_tree::fol::sigma_0::Formula,
        std::vec,
    };

    #[test]
    fn test_function_ordering_axioms() {
        let problem = Problem {
            name: "problem".into(),
            interpretation: Interpretation::Standard,
            preamble: None,
            formulas: vec![
                AnnotatedFormula {
                    name: "conjecture_0".into(),
                    role: Role::Conjecture,
                    formula: "p(f$s(a)) and q(f$s(b,c))".parse().unwrap(),
                },
                AnnotatedFormula {
                    name: "axiom_0".into(),
                    role: Role::Axiom,
                    formula: "forall X p( g$s(d) )".parse().unwrap(),
                },
            ],
        };
        let mut symbols = Vec::from_iter(problem.symbols().into_iter());
        symbols.sort();
        let max_symbol = symbols.pop().unwrap();
        let axioms = problem.function_ordering_axioms(max_symbol);

        let target: Vec<Formula> = vec![
            "forall X (d < f$s(X))".parse().unwrap(),
            "forall X Y (f$s(X) < g$s(Y))".parse().unwrap(),
            "forall X Y Y1 (g$s(X) < f$s(Y,Y1))".parse().unwrap(),
            "forall X Y (X < Y -> f$s(X) < f$s(Y))".parse().unwrap(),
            "forall X Y (X = Y <-> f$s(X) = f$s(Y))".parse().unwrap(),
            "forall X Y (X < Y -> g$s(X) < g$s(Y))".parse().unwrap(),
            "forall X Y (X = Y <-> g$s(X) = g$s(Y))".parse().unwrap(),
            "forall X X1 Y Y1 (X < Y -> f$s(X,X1) < f$s(Y,Y1))"
                .parse()
                .unwrap(),
            "forall X X1 Y Y1 ((X = Y and X1 < Y1) -> f$s(X,X1) < f$s(Y,Y1))"
                .parse()
                .unwrap(),
            "forall X X1 Y Y1 ((X = Y and X1 = Y1) <-> f$s(X,X1) = f$s(Y,Y1))"
                .parse()
                .unwrap(),
        ];
        for (i, f) in axioms.into_iter().enumerate() {
            let t = target[i].clone();
            assert_eq!(f, t, "\n{f} \n!=\n {t}");
        }
    }

    #[test]
    fn test_decomposition() {
        let problem = Problem {
            name: "problem".into(),
            interpretation: Interpretation::Standard,
            preamble: None,
            formulas: vec![
                AnnotatedFormula {
                    name: "axiom_0".into(),
                    role: Role::Axiom,
                    formula: "p(a)".parse().unwrap(),
                },
                AnnotatedFormula {
                    name: "axiom_1".into(),
                    role: Role::Axiom,
                    formula: "forall X p(X) -> q(X)".parse().unwrap(),
                },
                AnnotatedFormula {
                    name: "conjecture_0".into(),
                    role: Role::Conjecture,
                    formula: "p(a)".parse().unwrap(),
                },
                AnnotatedFormula {
                    name: "conjecture_1".into(),
                    role: Role::Conjecture,
                    formula: "q(a)".parse().unwrap(),
                },
            ],
        };

        assert_eq!(
            problem.decompose_independent(),
            vec![
                Problem {
                    name: "problem_0".into(),
                    interpretation: Interpretation::Standard,
                    preamble: None,
                    formulas: vec![
                        AnnotatedFormula {
                            name: "axiom_0".into(),
                            role: Role::Axiom,
                            formula: "p(a)".parse().unwrap(),
                        },
                        AnnotatedFormula {
                            name: "axiom_1".into(),
                            role: Role::Axiom,
                            formula: "forall X p(X) -> q(X)".parse().unwrap(),
                        },
                        AnnotatedFormula {
                            name: "conjecture_0".into(),
                            role: Role::Conjecture,
                            formula: "p(a)".parse().unwrap(),
                        },
                    ],
                },
                Problem {
                    name: "problem_1".into(),
                    interpretation: Interpretation::Standard,
                    preamble: None,
                    formulas: vec![
                        AnnotatedFormula {
                            name: "axiom_0".into(),
                            role: Role::Axiom,
                            formula: "p(a)".parse().unwrap(),
                        },
                        AnnotatedFormula {
                            name: "axiom_1".into(),
                            role: Role::Axiom,
                            formula: "forall X p(X) -> q(X)".parse().unwrap(),
                        },
                        AnnotatedFormula {
                            name: "conjecture_1".into(),
                            role: Role::Conjecture,
                            formula: "q(a)".parse().unwrap(),
                        },
                    ],
                }
            ]
        );

        assert_eq!(
            problem.decompose_sequential(),
            vec![
                Problem {
                    name: "problem_0".into(),
                    interpretation: Interpretation::Standard,
                    preamble: None,
                    formulas: vec![
                        AnnotatedFormula {
                            name: "axiom_0".into(),
                            role: Role::Axiom,
                            formula: "p(a)".parse().unwrap(),
                        },
                        AnnotatedFormula {
                            name: "axiom_1".into(),
                            role: Role::Axiom,
                            formula: "forall X p(X) -> q(X)".parse().unwrap(),
                        },
                        AnnotatedFormula {
                            name: "conjecture_0".into(),
                            role: Role::Conjecture,
                            formula: "p(a)".parse().unwrap(),
                        },
                    ],
                },
                Problem {
                    name: "problem_1".into(),
                    interpretation: Interpretation::Standard,
                    preamble: None,
                    formulas: vec![
                        AnnotatedFormula {
                            name: "axiom_0".into(),
                            role: Role::Axiom,
                            formula: "p(a)".parse().unwrap(),
                        },
                        AnnotatedFormula {
                            name: "axiom_1".into(),
                            role: Role::Axiom,
                            formula: "forall X p(X) -> q(X)".parse().unwrap(),
                        },
                        AnnotatedFormula {
                            name: "conjecture_0".into(),
                            role: Role::Axiom,
                            formula: "p(a)".parse().unwrap(),
                        },
                        AnnotatedFormula {
                            name: "conjecture_1".into(),
                            role: Role::Conjecture,
                            formula: "q(a)".parse().unwrap(),
                        },
                    ],
                }
            ]
        );
    }
}
