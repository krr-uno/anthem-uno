use {
    crate::{
        analyzing::{regularity::Regularity as _, tightness::Tightness},
        command_line::{
            Program,
            arguments::{
                Arguments, Command, Dialect, Equivalence, Output, ParseAs, Property,
                SimplificationPortfolio, SimplificationStrategy, Translation, Visualization,
            },
            files::Files,
        },
        convenience::{
            apply::Apply, compose::Compose, visualizing::formula_trees::grow_tree_from_formula,
        },
        simplifying::fol::sigma_0::{classic::CLASSIC, ht::HT, intuitionistic::INTUITIONISTIC},
        syntax_tree::{Node as _, asp, fol::sigma_0 as fol},
        translating::{
            classical_reduction::{completion::Completion as _, gamma::Gamma as _},
            formula_representation::{mu::Mu as _, natural::Natural as _, tau_star::TauStar as _},
        },
        verifying::{
            prover::{Prover, Report, Status, Success, vampire::Vampire},
            task::{
                Task, external_equivalence::ExternalEquivalenceTask,
                strong_equivalence::StrongEquivalenceTask,
            },
        },
    },
    anyhow::{Context, Result, anyhow},
    clap::Parser as _,
    either::Either,
    indexmap::IndexSet,
    petgraph::dot::{Config, Dot},
    std::{
        fs::{self, File},
        io::{self, Write, stdin},
        path::{Path, PathBuf},
        time::Instant,
    },
};

fn get_program_of_unknown_dialect(input: Option<PathBuf>) -> Result<Program> {
    let contents = match input {
        Some(path) => {
            let path: &Path = path.as_ref();
            fs::read_to_string(path)
                .with_context(|| format!("could not read file `{}`", path.display()))?
        }
        None => io::read_to_string(stdin()).with_context(|| "could not read from stdin")?,
    };

    match contents.parse::<asp::mini_gringo::Program>() {
        Ok(program) => Ok(Program::MiniGringo(program)),
        Err(_) => match contents.parse::<asp::mini_gringo_cl::Program>() {
            Ok(program) => Ok(Program::MiniGringoCl(program)),
            Err(e) => Err(e.into()),
        },
    }
}

pub fn main() -> Result<()> {
    match Arguments::parse().command {
        Command::Analyze {
            property,
            input,
            dialect,
        } => {
            match property {
                Property::Regularity => match dialect {
                    Dialect::MiniGringo => {
                        let program = input.map_or_else(
                            asp::mini_gringo::Program::from_stdin,
                            asp::mini_gringo::Program::from_file,
                        )?;
                        let is_regular = program.is_regular();
                        println!("{is_regular}");
                    }
                    Dialect::MiniGringoCL => {
                        println!("operation unsupported for mg-cl programs");
                    }
                },

                Property::Tightness => match dialect {
                    Dialect::MiniGringo => {
                        let program = input.map_or_else(
                            asp::mini_gringo::Program::from_stdin,
                            asp::mini_gringo::Program::from_file,
                        )?;
                        let intensional_predicates =
                            program.predicates().into_iter().map(|p| p.into()).collect();
                        let is_tight = program.is_tight(intensional_predicates);
                        println!("{is_tight}");
                    }
                    Dialect::MiniGringoCL => {
                        let program = input.map_or_else(
                            asp::mini_gringo_cl::Program::from_stdin,
                            asp::mini_gringo_cl::Program::from_file,
                        )?;
                        let intensional_predicates =
                            program.predicates().into_iter().map(|p| p.into()).collect();
                        let is_tight = program.tau_star().is_tight(intensional_predicates);
                        println!("{is_tight}");
                    }
                },
            }

            Ok(())
        }
        Command::Parse {
            r#as,
            output,
            input,
        } => {
            match r#as {
                ParseAs::MiniGringoProgram => {
                    let program = input.map_or_else(
                        asp::mini_gringo::Program::from_stdin,
                        asp::mini_gringo::Program::from_file,
                    )?;
                    match output {
                        Output::Debug => println!("{program:#?}"),
                        Output::Default => print!("{program}"),
                    }
                }
                ParseAs::MiniGringoCLProgram => {
                    let program = input.map_or_else(
                        asp::mini_gringo_cl::Program::from_stdin,
                        asp::mini_gringo_cl::Program::from_file,
                    )?;
                    match output {
                        Output::Debug => println!("{program:#?}"),
                        Output::Default => print!("{program}"),
                    }
                }
                ParseAs::Theory => {
                    let theory =
                        input.map_or_else(fol::Theory::from_stdin, fol::Theory::from_file)?;
                    match output {
                        Output::Debug => println!("{theory:#?}"),
                        Output::Default => print!("{theory}"),
                    }
                }
                ParseAs::Specification => {
                    let specification = input.map_or_else(
                        fol::Specification::from_stdin,
                        fol::Specification::from_file,
                    )?;
                    match output {
                        Output::Debug => println!("{specification:#?}"),
                        Output::Default => print!("{specification}"),
                    }
                }
                ParseAs::UserGuide => {
                    let user_guide =
                        input.map_or_else(fol::UserGuide::from_stdin, fol::UserGuide::from_file)?;
                    match output {
                        Output::Debug => println!("{user_guide:#?}"),
                        Output::Default => print!("{user_guide}"),
                    }
                }
            };

            Ok(())
        }
        Command::Simplify {
            portfolio,
            strategy,
            input,
        } => {
            let mut simplification = match portfolio {
                SimplificationPortfolio::Classic => [INTUITIONISTIC, HT, CLASSIC].concat(),
                SimplificationPortfolio::Ht => [INTUITIONISTIC, HT].concat(),
                SimplificationPortfolio::Intuitionistic => [INTUITIONISTIC].concat(),
            }
            .into_iter()
            .compose();

            let theory = input.map_or_else(fol::Theory::from_stdin, fol::Theory::from_file)?;

            let simplified_theory: fol::Theory = theory
                .into_iter()
                .map(|formula| match strategy {
                    SimplificationStrategy::Shallow => simplification(formula),
                    SimplificationStrategy::Recursive => formula.apply(&mut simplification),
                    SimplificationStrategy::Fixpoint => formula.apply_fixpoint(&mut simplification),
                })
                .collect();

            print!("{simplified_theory}");

            Ok(())
        }
        Command::Translate { with, input } => {
            match with {
                Translation::Completion => {
                    let theory =
                        input.map_or_else(fol::Theory::from_stdin, fol::Theory::from_file)?;
                    let completed_theory = theory
                        .completion(IndexSet::new())
                        .context("the given theory is not completable")?;
                    print!("{completed_theory}")
                }

                Translation::Gamma => {
                    let theory =
                        input.map_or_else(fol::Theory::from_stdin, fol::Theory::from_file)?;
                    let gamma_theory = theory.gamma();
                    print!("{gamma_theory}")
                }

                Translation::Mu => {
                    let program = get_program_of_unknown_dialect(input)?;
                    match program {
                        Program::MiniGringo(program) => {
                            let theory = program.mu();
                            print!("{theory}")
                        }
                        Program::MiniGringoCl(_) => todo!(),
                    }
                }

                Translation::Natural => {
                    let program = get_program_of_unknown_dialect(input)?;
                    match program {
                        Program::MiniGringo(program) => {
                            let theory = program
                                .natural()
                                .context("the given program is not regular")?;
                            print!("{theory}")
                        }
                        Program::MiniGringoCl(_) => todo!(),
                    }
                }

                Translation::TauStar => {
                    let program = get_program_of_unknown_dialect(input)?;
                    let theory = program.tau_star();
                    print!("{theory}")
                }
            }

            Ok(())
        }
        Command::Verify {
            equivalence,
            decomposition,
            direction,
            bypass_tightness,
            no_simplify,
            no_eq_break,
            no_proof_search,
            no_timing,
            time_limit,
            prover_instances,
            prover_cores,
            save_problems: out_dir,
            files,
            dialect,
        } => {
            let start_time = Instant::now();

            let files =
                Files::sort(files).context("unable to sort the given files by their function")?;

            let problems = match equivalence {
                Equivalence::Strong => match dialect {
                    Dialect::MiniGringoCL => StrongEquivalenceTask {
                        left: asp::mini_gringo_cl::Program::from_file(
                            files
                                .left()
                                .ok_or(anyhow!("no left program was provided"))?,
                        )?,
                        right: asp::mini_gringo_cl::Program::from_file(
                            files
                                .right()
                                .ok_or(anyhow!("no right program was provided"))?,
                        )?,
                        decomposition,
                        direction,
                        simplify: !no_simplify,
                        break_equivalences: !no_eq_break,
                    }
                    .decompose()?
                    .report_warnings(),

                    Dialect::MiniGringo => {
                        let left = asp::mini_gringo::Program::from_file(
                            files
                                .left()
                                .ok_or(anyhow!("no left program was provided"))?,
                        )?;
                        let right = asp::mini_gringo::Program::from_file(
                            files
                                .right()
                                .ok_or(anyhow!("no right program was provided"))?,
                        )?;

                        StrongEquivalenceTask {
                            left: left.into(),
                            right: right.into(),
                            decomposition,
                            direction,
                            simplify: !no_simplify,
                            break_equivalences: !no_eq_break,
                        }
                        .decompose()?
                        .report_warnings()
                    }
                },

                Equivalence::External => match dialect {
                    Dialect::MiniGringoCL => ExternalEquivalenceTask {
                        specification: match files
                            .specification()
                            .ok_or(anyhow!("no specification was provided"))?
                        {
                            Either::Left(program) => {
                                Either::Left(asp::mini_gringo_cl::Program::from_file(program)?)
                            }
                            Either::Right(specification) => {
                                Either::Right(fol::Specification::from_file(specification)?)
                            }
                        },
                        program: asp::mini_gringo_cl::Program::from_file(
                            files.program().ok_or(anyhow!("no program was provided"))?,
                        )?,
                        user_guide: fol::UserGuide::from_file(
                            files
                                .user_guide()
                                .ok_or(anyhow!("no user guide was provided"))?,
                        )?,
                        proof_outline: files
                            .proof_outline()
                            .map(fol::Specification::from_file)
                            .unwrap_or_else(|| Ok(fol::Specification::empty()))?,
                        decomposition,
                        direction,
                        bypass_tightness,
                        simplify: !no_simplify,
                        break_equivalences: !no_eq_break,
                    }
                    .decompose()?
                    .report_warnings(),

                    Dialect::MiniGringo => {
                        let specification = match files
                            .specification()
                            .ok_or(anyhow!("no specification was provided"))?
                        {
                            Either::Left(program) => {
                                let program = asp::mini_gringo::Program::from_file(program)?;
                                Either::Left(program.into())
                            }
                            Either::Right(specification) => {
                                Either::Right(fol::Specification::from_file(specification)?)
                            }
                        };

                        let program = asp::mini_gringo::Program::from_file(
                            files.program().ok_or(anyhow!("no program was provided"))?,
                        )?;

                        ExternalEquivalenceTask {
                            specification: specification.into(),
                            program: program.into(),
                            user_guide: fol::UserGuide::from_file(
                                files
                                    .user_guide()
                                    .ok_or(anyhow!("no user guide was provided"))?,
                            )?,
                            proof_outline: files
                                .proof_outline()
                                .map(fol::Specification::from_file)
                                .unwrap_or_else(|| Ok(fol::Specification::empty()))?,
                            decomposition,
                            direction,
                            bypass_tightness,
                            simplify: !no_simplify,
                            break_equivalences: !no_eq_break,
                        }
                        .decompose()?
                        .report_warnings()
                    }
                },
            };

            if let Some(out_dir) = out_dir {
                for problem in &problems {
                    let mut path = out_dir.clone();
                    path.push(format!("{}.p", problem.name));
                    problem.to_file(path)?;
                }
            }

            if !no_proof_search {
                let prover = Vampire {
                    time_limit,
                    instances: prover_instances,
                    cores: prover_cores,
                };

                let problems = problems.into_iter().inspect(|problem| {
                    println!("> Proving {}...", problem.name);
                    println!("Axioms:");
                    for axiom in problem.axioms() {
                        println!("    {}", axiom.formula);
                    }
                    println!();
                    println!("Conjectures:");
                    for conjecture in problem.conjectures() {
                        println!("    {}", conjecture.formula);
                    }
                    println!();
                });

                let mut success = true;
                for result in prover.prove_all(problems) {
                    match result {
                        Ok(report) => match report.status() {
                            Ok(status) => {
                                println!(
                                    "> Proving {} ended with a SZS status",
                                    report.problem.name
                                );
                                print!("Status: {status}");
                                if !no_timing {
                                    print!(" ({} ms)", report.elapsed_time.as_millis())
                                }
                                println!();
                                if !matches!(status, Status::Success(Success::Theorem)) {
                                    success = false;
                                }
                            }
                            Err(error) => {
                                println!(
                                    "> Proving {} ended without a SZS status",
                                    report.problem.name
                                );
                                println!("Output/stdout:");
                                println!("{}", report.output.stdout);
                                println!("Output/stderr:");
                                println!("{}", report.output.stderr);
                                println!("Error: {error}");
                                success = false;
                            }
                        },
                        Err(error) => {
                            println!("> Proving <a problem> ended with an error"); // TODO: Get the name of the problem
                            println!("Error: {error}");
                            success = false;
                        }
                    }
                    println!();
                }

                if success {
                    print!("> Success! Anthem found a proof of the theorem.")
                } else {
                    print!("> Failure! Anthem was unable to find a proof of the theorem.")
                }

                if !no_timing {
                    print!(" ({} ms)", start_time.elapsed().as_millis())
                }

                println!()
            }

            Ok(())
        }

        Command::Visualize {
            input,
            property,
            save_visualization,
        } => {
            let theory = input.map_or_else(fol::Theory::from_stdin, fol::Theory::from_file)?;

            let output = match property {
                Visualization::Ast => {
                    let formula = fol::Formula::conjoin(theory);
                    let (_, tree) = grow_tree_from_formula(formula);
                    format!("{}", Dot::with_config(&tree, &[Config::EdgeNoLabel]))
                }
                Visualization::DependencyGraph => {
                    // TODO: allow user to specify set of intensional predicates
                    let intensional_predicates = theory.predicates();
                    match theory.predicate_dependency_graph(intensional_predicates) {
                        Some(graph) => {
                            format!("{}", Dot::with_config(&graph, &[Config::EdgeNoLabel]))
                        }
                        _ => "".to_string(),
                    }
                }
            };

            let mut f = File::create(save_visualization).unwrap();
            f.write_all(output.as_bytes())?;

            Ok(())
        }
    }
}
