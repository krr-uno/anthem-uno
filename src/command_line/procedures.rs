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
        formatting::fol::sigma_0::latex,
        simplifying::fol::sigma_0::{classic::CLASSIC, ht::HT, intuitionistic::INTUITIONISTIC},
        syntax_tree::{Node as _, asp, fol::sigma_0 as fol},
        translating::{
            classical_reduction::{completion::Completion as _, gamma::Gamma as _},
            formula_representation::{mu::Mu as _, natural::Natural as _, tau_star::TauStar as _},
        },
        verifying::{
            problem::Interpretation,
            prover::{Prover, Report, Status, Success, vampire::Vampire},
            task::{
                Task,
                external_equivalence::ExternalEquivalenceTask,
                strong_equivalence::{StrongEquivalenceCounterModelTask, StrongEquivalenceTask},
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
        process,
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

fn convert_to_smt2(path: PathBuf) -> Result<()> {
    let fname = path.display().to_string();

    let child = process::Command::new("./cvc5-tptp-to-smt2")
        .args([
            "-o",
            "raw-benchmark",
            "--parse-only",
            "--lang=tptp",
            "--output-lang=smt2",
            &fname,
        ])
        .stdout(process::Stdio::piped())
        .stderr(process::Stdio::piped())
        .spawn()?;

    let output = child.wait_with_output()?;

    fs::write(path.with_extension("smt2"), output.stdout).expect("Unable to write file");

    Ok(())
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
            display_latex,
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

            if display_latex {
                let theory = latex::Format(&simplified_theory);
                print!("{theory}");
            } else {
                print!("{simplified_theory}");
            }

            Ok(())
        }

        Command::Translate {
            with,
            input,
            display_latex,
        } => {
            let theory = match with {
                Translation::Completion => {
                    let theory: fol::Theory = match input {
                        Some(path) => match fol::Theory::from_file(&path) {
                            Ok(theory) => Ok(theory),
                            Err(_) => match asp::mini_gringo::Program::from_file(path) {
                                Ok(program) => Ok(program.tau_star()),
                                Err(e) => Err(e),
                            },
                        },
                        None => match fol::Theory::from_stdin() {
                            Ok(theory) => Ok(theory),
                            Err(_) => match asp::mini_gringo::Program::from_stdin() {
                                Ok(program) => Ok(program.tau_star()),
                                Err(e) => Err(e),
                            },
                        },
                    }?;

                    theory
                        .completion(IndexSet::new())
                        .context("the given theory is not completable")?
                }

                Translation::Gamma => {
                    let theory =
                        input.map_or_else(fol::Theory::from_stdin, fol::Theory::from_file)?;
                    theory.gamma()
                }

                Translation::Mu => {
                    let program = get_program_of_unknown_dialect(input)?;
                    match program {
                        Program::MiniGringo(program) => program.mu(),
                        Program::MiniGringoCl(_) => todo!(),
                    }
                }

                Translation::Natural => {
                    let program = get_program_of_unknown_dialect(input)?;
                    match program {
                        Program::MiniGringo(program) => program
                            .natural(false)
                            .context("the given program is not regular")?,
                        Program::MiniGringoCl(_) => todo!(),
                    }
                }

                Translation::TauStar => {
                    let program = get_program_of_unknown_dialect(input)?;
                    program.tau_star()
                }
            };

            if display_latex {
                let theory = latex::Format(&theory);
                print!("{theory}")
            } else {
                print!("{theory}")
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
            induction,
            no_proof_search,
            no_timing,
            time_limit,
            prover_instances,
            prover_cores,
            save_problems: out_dir,
            files,
            dialect,
            formula_representation,
            backend,
            countermodel,
        } => {
            let start_time = Instant::now();

            let files =
                Files::sort(files).context("unable to sort the given files by their function")?;

            let (problems, countermodel_task) = match equivalence {
                Equivalence::Strong => match dialect {
                    Dialect::MiniGringoCL => {
                        let left = asp::mini_gringo_cl::Program::from_file(
                            files
                                .left()
                                .ok_or(anyhow!("no left program was provided"))?,
                        )?;
                        let right = asp::mini_gringo_cl::Program::from_file(
                            files
                                .right()
                                .ok_or(anyhow!("no right program was provided"))?,
                        )?;

                        (
                            StrongEquivalenceTask {
                                left: left.clone(),
                                right: right.clone(),
                                decomposition,
                                direction,
                                simplify: !no_simplify,
                                break_equivalences: !no_eq_break,
                            }
                            .decompose()?
                            .report_warnings(),
                            Some(StrongEquivalenceCounterModelTask {
                                left,
                                right,
                                simplify: !no_simplify,
                            }),
                        )
                    }

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

                        (
                            StrongEquivalenceTask {
                                left: left.clone().into(),
                                right: right.clone().into(),
                                decomposition,
                                direction,
                                simplify: !no_simplify,
                                break_equivalences: !no_eq_break,
                            }
                            .decompose()?
                            .report_warnings(),
                            Some(StrongEquivalenceCounterModelTask {
                                left: left.into(),
                                right: right.into(),
                                simplify: !no_simplify,
                            }),
                        )
                    }
                },

                Equivalence::External => match dialect {
                    Dialect::MiniGringoCL => (
                        ExternalEquivalenceTask {
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
                            formula_representation,
                            bypass_tightness,
                            simplify: !no_simplify,
                            break_equivalences: !no_eq_break,
                        }
                        .decompose()?
                        .report_warnings(),
                        None,
                    ),

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

                        (
                            ExternalEquivalenceTask {
                                specification,
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
                                formula_representation,
                                bypass_tightness,
                                simplify: !no_simplify,
                                break_equivalences: !no_eq_break,
                            }
                            .decompose()?
                            .report_warnings(),
                            None,
                        )
                    }
                },
            };

            if let Some(out_dir) = out_dir {
                // TODO: match on Interpretation
                let mut preamble_path = out_dir.clone();
                preamble_path.push("standard_preamble.p");
                // Write preamble to separate file
                Interpretation::Standard.to_file(&preamble_path)?;

                for problem in &problems {
                    let mut path = out_dir.clone();
                    path.push(format!("{}.p", problem.name));
                    let mut problem = problem.clone();
                    problem.preamble = Some(PathBuf::from("standard_preamble.p"));
                    problem.to_file(path)?;
                }

                // emit countermodel task
                if countermodel {
                    if let Some(task) = countermodel_task {
                        let countermodel_problems = task.decompose()?.report_warnings();
                        assert_eq!(
                            countermodel_problems.len(),
                            1,
                            "countermodel task should only have one problem file"
                        );
                        let counter_problem = countermodel_problems[0].clone();
                        let mut path = out_dir.clone();
                        path.push(format!("{}.p", counter_problem.name));
                        counter_problem.to_file(path.clone())?;
                        convert_to_smt2(path)?;
                    }
                }
            }

            if !no_proof_search {
                let prover = Vampire {
                    instances: prover_instances,
                    cores: prover_cores,
                    backend,
                    induction,
                    time_limit,
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
            save_as,
        } => {
            let input = match input {
                Some(path) => {
                    match fol::Theory::from_file(&path) {
                        Ok(theory) => Ok(Either::Left(theory)),
                        Err(_) => match get_program_of_unknown_dialect(Some(path)) {
                            Ok(program) => Ok(Either::Right(program)),
                            Err(e) => Err(e),
                        },
                    }
                }?,
                None => {
                    todo!()
                }
            };

            let output = match property {
                Visualization::Ast => match input {
                    Either::Left(theory) => {
                        let formula = fol::Formula::conjoin(theory);
                        let (_, tree) = grow_tree_from_formula(formula);
                        Ok(format!(
                            "{}",
                            Dot::with_config(&tree, &[Config::EdgeNoLabel])
                        ))
                    }
                    Either::Right(_) => {
                        Err(anyhow!("AST visualization is not supported for programs"))
                    }
                },

                Visualization::DependencyGraph => {
                    match input {
                        Either::Left(theory) => {
                            // TODO: allow user to specify set of intensional predicates
                            let intensional_predicates = theory.predicates();
                            match theory.predicate_dependency_graph(intensional_predicates) {
                                Some(graph) => Ok(format!(
                                    "{}",
                                    Dot::with_config(&graph, &[Config::EdgeNoLabel])
                                )),
                                _ => Err(anyhow!("could not generate dependency graph of theory")),
                            }
                        }
                        Either::Right(prog) => {
                            let graph = match prog {
                                Program::MiniGringo(program) => {
                                    let intensional_predicates = program.predicates();
                                    program.predicate_dependency_graph(intensional_predicates)
                                }
                                Program::MiniGringoCl(program) => {
                                    let intensional_predicates = program.predicates();
                                    program.predicate_dependency_graph(intensional_predicates)
                                }
                            };
                            Ok(format!(
                                "{}",
                                Dot::with_config(&graph, &[Config::EdgeNoLabel])
                            ))
                        }
                    }
                }
            }?;

            let mut graph_out = save_as.clone();
            graph_out.set_extension("dot");
            let graphvis_file = graph_out.clone();

            let mut pdf_file = graph_out.clone();
            pdf_file.set_extension("pdf");

            let mut f = File::create(graph_out).unwrap();
            f.write_all(output.as_bytes())?;

            let dot_cmd = format!(
                "dot -Tpdf {} > {}",
                graphvis_file.display(),
                pdf_file.display()
            );

            process::Command::new("sh")
                .arg("-c")
                .arg(dot_cmd)
                .output()
                .expect("could not run dot command");

            Ok(())
        }
    }
}
