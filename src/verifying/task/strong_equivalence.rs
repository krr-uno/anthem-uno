use {
    crate::{
        command_line::arguments::Decomposition,
        convenience::{
            apply::Apply as _,
            compose::Compose as _,
            with_warnings::{Result, WithWarnings},
        },
        simplifying::fol::sigma_0::{classic::CLASSIC, ht::HT, intuitionistic::INTUITIONISTIC},
        syntax_tree::{GenericPredicate, asp::mini_gringo_cl as asp, fol::sigma_0 as fol},
        translating::{
            classical_reduction::gamma::{Gamma as _, Here as _, There as _},
            formula_representation::tau_star::TauStar,
        },
        verifying::{
            problem::{self, AnnotatedFormula, Problem, Role},
            task::Task,
        },
    },
    indexmap::IndexMap,
    std::fmt::Display,
    thiserror::Error,
};

#[derive(Error, Debug)]
pub enum StrongEquivalenceTaskWarning {
    InvalidRoleWithinUserGuide(fol::AnnotatedFormula),
    UserGuideContainsPredicateDeclarations(fol::Predicate),
}

impl Display for StrongEquivalenceTaskWarning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StrongEquivalenceTaskWarning::InvalidRoleWithinUserGuide(formula) => writeln!(
                f,
                "the following formula is ignored because user guides only permit assumptions: {formula}"
            ),
            StrongEquivalenceTaskWarning::UserGuideContainsPredicateDeclarations(predicate) => {
                writeln!(
                    f,
                    "input/output predicate declarations, e.g. {predicate}, are not appropriate for strong equivalence user guides"
                )
            }
        }
    }
}

#[derive(Error, Debug)]
pub enum StrongEquivalenceTaskError {
    PredicateInUserGuideAssumption(fol::AnnotatedFormula),
}

impl Display for StrongEquivalenceTaskError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StrongEquivalenceTaskError::PredicateInUserGuideAssumption(formula) => {
                writeln!(
                    f,
                    "the following user guide assumption contains a non-arithmetic predicate: {formula}"
                )
            }
        }
    }
}

pub struct StrongEquivalenceTask {
    pub left: asp::Program,
    pub right: asp::Program,
    pub user_guide: Option<fol::UserGuide>,
    pub decomposition: Decomposition,
    pub direction: fol::Direction,
    pub simplify: bool,
    pub break_equivalences: bool,
}

impl StrongEquivalenceTask {
    fn transition_axioms(&self) -> fol::Theory {
        fn transition(p: asp::Predicate) -> fol::Formula {
            let p: fol::Predicate = GenericPredicate::from(p).into();

            let hp = p.clone().to_formula().here();
            let tp = p.to_formula().there();

            let variables = hp.free_variables();

            fol::Formula::BinaryFormula {
                connective: fol::BinaryConnective::Implication,
                lhs: hp.into(),
                rhs: tp.into(),
            }
            .quantify(fol::Quantifier::Forall, variables.into_iter().collect())
        }

        let mut predicates = self.left.predicates();
        predicates.extend(self.right.predicates());

        fol::Theory {
            formulas: predicates.into_iter().map(transition).collect(),
        }
    }

    fn ensure_absence_of_predicate_declarations(
        &self,
    ) -> Result<(), StrongEquivalenceTaskWarning, StrongEquivalenceTaskError> {
        if let Some(ug) = &self.user_guide {
            for entry in ug.entries.iter() {
                match entry {
                    fol::UserGuideEntry::InputPredicate(predicate)
                    | fol::UserGuideEntry::OutputPredicate(predicate) => {
                        return Ok(WithWarnings::flawless(()).add_warning(
                            StrongEquivalenceTaskWarning::UserGuideContainsPredicateDeclarations(
                                predicate.clone(),
                            ),
                        ));
                    }
                    _ => (),
                }
            }
        }

        Ok(WithWarnings::flawless(()))
    }
}

impl Task for StrongEquivalenceTask {
    type Error = StrongEquivalenceTaskError;
    type Warning = StrongEquivalenceTaskWarning;

    fn decompose(self) -> Result<Vec<Problem>, Self::Warning, Self::Error> {
        let mut warnings = self.ensure_absence_of_predicate_declarations()?.warnings;

        let transition_axioms = self.transition_axioms(); // These are the "forall X (hp(X) -> tp(X))" axioms.

        let mut left = self.left.tau_star();
        let mut right = self.right.tau_star();

        let placeholders = match &self.user_guide {
            Some(ug) => ug
                .placeholders()
                .into_iter()
                .map(|p| (p.name.clone(), p))
                .collect(),
            None => IndexMap::new(),
        };

        left = left.replace_placeholders(&placeholders);
        right = right.replace_placeholders(&placeholders);

        if self.simplify {
            let mut portfolio = [INTUITIONISTIC, HT].concat().into_iter().compose();
            left = left
                .into_iter()
                .map(|f| f.apply_fixpoint(&mut portfolio))
                .collect();
            right = right
                .into_iter()
                .map(|f| f.apply_fixpoint(&mut portfolio))
                .collect();
        }

        left = left.gamma();
        right = right.gamma();

        if self.simplify {
            let mut portfolio = [INTUITIONISTIC, HT, CLASSIC].concat().into_iter().compose();
            left = left
                .into_iter()
                .map(|f| f.apply_fixpoint(&mut portfolio))
                .collect();
            right = right
                .into_iter()
                .map(|f| f.apply_fixpoint(&mut portfolio))
                .collect();
        }

        if self.break_equivalences {
            left = crate::breaking::fol::sigma_0::ht::break_equivalences_theory(left);
            right = crate::breaking::fol::sigma_0::ht::break_equivalences_theory(right);
        }

        let mut user_guide_assumptions = Vec::new();
        if let Some(ug) = self.user_guide {
            for formula in ug.formulas() {
                match formula.role {
                    fol::Role::Assumption => {
                        // Assumptions should be purely `arithmetic`
                        if formula.predicates().is_empty() {
                            user_guide_assumptions
                                .push(formula.replace_placeholders(&placeholders));
                        } else {
                            return Err(
                                StrongEquivalenceTaskError::PredicateInUserGuideAssumption(formula),
                            );
                        }
                    }
                    _ => warnings.push(StrongEquivalenceTaskWarning::InvalidRoleWithinUserGuide(
                        formula,
                    )),
                }
            }
        }

        Ok(ValidatedStrongEquivalenceTask {
            left,
            right,
            user_guide_assumptions,
            transition_axioms,
            decomposition: self.decomposition,
            direction: self.direction,
        }
        .decompose()?
        .preface_warnings(warnings))
    }
}

struct ValidatedStrongEquivalenceTask {
    pub left: fol::Theory,
    pub right: fol::Theory,
    pub user_guide_assumptions: Vec<fol::AnnotatedFormula>,
    pub transition_axioms: fol::Theory,
    //pub proof_outline: ProofOutline,
    pub decomposition: Decomposition,
    pub direction: fol::Direction,
}

impl Task for ValidatedStrongEquivalenceTask {
    type Error = StrongEquivalenceTaskError;
    type Warning = StrongEquivalenceTaskWarning;

    fn decompose(self) -> Result<Vec<Problem>, Self::Warning, Self::Error> {
        let stable_premises: Vec<_> = self
            .user_guide_assumptions
            .into_iter()
            .map(|a| a.into_problem_formula(problem::Role::Axiom))
            .collect();

        let mut problems = Vec::new();
        if matches!(
            self.direction,
            fol::Direction::Universal | fol::Direction::Forward
        ) {
            problems.push(
                Problem::with_name("forward")
                    .add_theory(self.transition_axioms.clone(), |i, formula| {
                        AnnotatedFormula {
                            name: format!("transition_axiom_{i}"),
                            role: Role::Axiom,
                            formula,
                        }
                    })
                    .add_annotated_formulas(stable_premises.clone())
                    .add_theory(self.left.clone(), |i, formula| AnnotatedFormula {
                        name: format!("left_{i}"),
                        role: Role::Axiom,
                        formula,
                    })
                    .add_theory(self.right.clone(), |i, formula| AnnotatedFormula {
                        name: format!("right_{i}"),
                        role: Role::Conjecture,
                        formula,
                    })
                    .rename_conflicting_symbols()
                    .create_unique_formula_names(),
            );
        }
        if matches!(
            self.direction,
            fol::Direction::Universal | fol::Direction::Backward
        ) {
            problems.push(
                Problem::with_name("backward")
                    .add_theory(self.transition_axioms, |i, formula| AnnotatedFormula {
                        name: format!("transition_axiom_{i}"),
                        role: Role::Axiom,
                        formula,
                    })
                    .add_annotated_formulas(stable_premises)
                    .add_theory(self.right, |i, formula| AnnotatedFormula {
                        name: format!("right_{i}"),
                        role: Role::Axiom,
                        formula,
                    })
                    .add_theory(self.left, |i, formula| AnnotatedFormula {
                        name: format!("left_{i}"),
                        role: Role::Conjecture,
                        formula,
                    })
                    .rename_conflicting_symbols()
                    .create_unique_formula_names(),
            );
        }

        Ok(WithWarnings::flawless(
            problems
                .into_iter()
                .flat_map(|p: Problem| match self.decomposition {
                    Decomposition::Independent => p.decompose_independent(),
                    Decomposition::Sequential => p.decompose_sequential(),
                })
                .collect(),
        ))
    }
}
