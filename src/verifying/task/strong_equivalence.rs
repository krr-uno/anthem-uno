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
            outline::{ProofOutline, ProofOutlineError, ProofOutlineWarning},
            problem::{self, AnnotatedFormula, Problem, Role},
            task::Task,
        },
    },
    indexmap::{IndexMap, IndexSet},
    std::fmt::Display,
    thiserror::Error,
};

fn ensure_absence_of_definitions(
    outline: &ProofOutline,
) -> Result<(), StrongEquivalenceTaskWarning, StrongEquivalenceTaskError> {
    if let Some(definition) = outline.forward_definitions.first() {
        Err(StrongEquivalenceTaskError::ProofOutlineContainsDefinition(
            definition.clone(),
        ))
    } else if let Some(definition) = outline.backward_definitions.first() {
        Err(StrongEquivalenceTaskError::ProofOutlineContainsDefinition(
            definition.clone(),
        ))
    } else {
        Ok(WithWarnings::flawless(()))
    }
}

#[derive(Error, Debug)]
pub enum StrongEquivalenceTaskWarning {
    InvalidRoleWithinUserGuide(fol::AnnotatedFormula),
    UserGuideContainsPredicateDeclarations(fol::Predicate),
    DefinitionWithWarning(#[from] ProofOutlineWarning),
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
            StrongEquivalenceTaskWarning::DefinitionWithWarning(warning) => {
                writeln!(f, "{warning}")
            }
        }
    }
}

#[derive(Error, Debug)]
pub enum StrongEquivalenceTaskError {
    PredicateInUserGuideAssumption(fol::AnnotatedFormula),
    ProofOutlineError(#[from] ProofOutlineError),
    ProofOutlineContainsDefinition(fol::AnnotatedFormula),
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
            StrongEquivalenceTaskError::ProofOutlineError(error) => {
                writeln!(f, "the given proof outline contains errors: {error}")
            }
            StrongEquivalenceTaskError::ProofOutlineContainsDefinition(formula) => {
                writeln!(
                    f,
                    "strong equivalence proof outlines do not support definitions, e.g. {formula}"
                )
            }
        }
    }
}

pub struct StrongEquivalenceTask {
    pub left: asp::Program,
    pub right: asp::Program,
    pub user_guide: Option<fol::UserGuide>,
    pub proof_outline: fol::Specification,
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

        let mut taken_predicates = IndexSet::new();
        for formula in left.formulas.iter() {
            taken_predicates.extend(formula.predicates());
        }
        for formula in right.formulas.iter() {
            taken_predicates.extend(formula.predicates());
        }

        let proof_outline_construction =
            ProofOutline::from_specification(self.proof_outline, taken_predicates, &placeholders)?;
        warnings.extend(
            proof_outline_construction
                .warnings
                .into_iter()
                .map(StrongEquivalenceTaskWarning::from),
        );

        let proof_outline = proof_outline_construction.data;
        ensure_absence_of_definitions(&proof_outline)?;

        Ok(ValidatedStrongEquivalenceTask {
            left,
            right,
            user_guide_assumptions,
            transition_axioms,
            proof_outline,
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
    pub proof_outline: ProofOutline,
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

        let proof_outline = self.proof_outline.apply_gamma_reduction();

        let mut problems = Vec::new();
        if matches!(
            self.direction,
            fol::Direction::Universal | fol::Direction::Forward
        ) {
            let mut forward_axioms = stable_premises.clone();

            for (i, lemma) in proof_outline.forward_lemmas.iter().enumerate() {
                for (j, conjecture) in lemma.conjectures.iter().enumerate() {
                    problems.push(
                        Problem::with_name(format!("forward_outline_{i}_{j}"))
                            .add_theory(self.transition_axioms.clone(), |i, formula| {
                                AnnotatedFormula {
                                    name: format!("transition_axiom_{i}"),
                                    role: Role::Axiom,
                                    formula,
                                }
                            })
                            .add_annotated_formulas(forward_axioms.clone())
                            .add_theory(self.left.clone(), |i, formula| AnnotatedFormula {
                                name: format!("left_{i}"),
                                role: Role::Axiom,
                                formula,
                            })
                            .add_annotated_formulas(std::iter::once(conjecture.clone()))
                            .rename_conflicting_symbols()
                            .create_unique_formula_names(),
                    );
                }
                // Expand the axiom set
                forward_axioms.append(&mut lemma.consequences.clone());
            }

            // Add the Forward problems to problem list
            problems.append(
                &mut Problem::with_name("forward")
                    .add_theory(self.transition_axioms.clone(), |i, formula| {
                        AnnotatedFormula {
                            name: format!("transition_axiom_{i}"),
                            role: Role::Axiom,
                            formula,
                        }
                    })
                    .add_annotated_formulas(forward_axioms)
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
                    .create_unique_formula_names()
                    .decompose(self.decomposition),
            );
        }
        if matches!(
            self.direction,
            fol::Direction::Universal | fol::Direction::Backward
        ) {
            let mut backward_axioms = stable_premises;

            for (i, lemma) in proof_outline.backward_lemmas.iter().enumerate() {
                for (j, conjecture) in lemma.conjectures.iter().enumerate() {
                    problems.push(
                        Problem::with_name(format!("backward_outline_{i}_{j}"))
                            .add_theory(self.transition_axioms.clone(), |i, formula| {
                                AnnotatedFormula {
                                    name: format!("transition_axiom_{i}"),
                                    role: Role::Axiom,
                                    formula,
                                }
                            })
                            .add_annotated_formulas(backward_axioms.clone())
                            .add_theory(self.right.clone(), |i, formula| AnnotatedFormula {
                                name: format!("right_{i}"),
                                role: Role::Axiom,
                                formula,
                            })
                            .add_annotated_formulas(std::iter::once(conjecture.clone()))
                            .rename_conflicting_symbols()
                            .create_unique_formula_names(),
                    );
                }
                backward_axioms.append(&mut lemma.consequences.clone());
            }

            problems.append(
                &mut Problem::with_name("backward")
                    .add_theory(self.transition_axioms, |i, formula| AnnotatedFormula {
                        name: format!("transition_axiom_{i}"),
                        role: Role::Axiom,
                        formula,
                    })
                    .add_annotated_formulas(backward_axioms)
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
                    .create_unique_formula_names()
                    .decompose(self.decomposition),
            );
        }

        Ok(WithWarnings::flawless(problems))
    }
}
