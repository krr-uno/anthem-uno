use {
    crate::verifying::{
        model_builder::{
            Assignment, Failure, Model, ModelBuilder, ModelExtractionError, Report, Status, StatusExtractionError, Success,
        }, problem::smtlib::Problem,
    }, lazy_static::lazy_static, regex::Regex, std::{
        fmt::{self, Display},
        io::Write as _,
        process::{Command, Output, Stdio},
        //time::{Duration, Instant},
    }, thiserror::Error,
};

lazy_static! {
    static ref STATUS: Regex =
        Regex::new(r"no model found").unwrap();
}

#[derive(Error, Debug)]
pub enum FestError {
    #[error("unable to spawn Fest as a child process")]
    Spawn(#[source] std::io::Error),
    #[error("unable to write to Fest's stdin")]
    Write(#[source] std::io::Error),
    #[error("unable to wait for Fest")]
    Wait(#[source] std::io::Error),
    #[error("unable to convert output")]
    ConvertOutput(#[source] std::string::FromUtf8Error),
}

#[derive(Debug, Clone)]
pub struct FestOutput {
    pub stdout: String,
    pub stderr: String,
}

impl TryFrom<Output> for FestOutput {
    type Error = FestError;

    fn try_from(value: Output) -> Result<Self, Self::Error> {
        Ok(FestOutput {
            stdout: String::from_utf8(value.stdout).map_err(FestError::ConvertOutput)?,
            stderr: String::from_utf8(value.stderr).map_err(FestError::ConvertOutput)?,
        })
    }
}

#[derive(Debug, Clone)]
pub struct FestReport {
    pub problem: Problem,
    pub output: FestOutput,
    //pub elapsed_time: Duration,
}

impl Report for FestReport {
    fn status(&self) -> Result<Status, StatusExtractionError> {
        if let Some(_) = STATUS.captures(&self.output.stdout) {
            Ok(Status::Failure(Failure::Unknown))
        } else {
            if self.output.stderr.is_empty() {
                Ok(Status::Success(Success::Satisfiable))
            } else {
                Ok(Status::Failure(Failure::Unknown))
            }
        }
    }

    fn model(&self) -> Result<Option<Model>, ModelExtractionError> {
        match self.status() {
            Ok(status) => match status {
                Status::Success(success) => match success {
                    Success::Satisfiable => {
                        let mut assignments = Vec::new();

                        let output = &self.output.stdout;
                        let mut lines = output.lines();
                        lines.next(); // Discard the model name
                        for line in lines {
                            assignments.push(Assignment {
                                raw: line.to_string(),
                            });
                        }

                        Ok(Some(Model { assignments }))
                    }
                },
                Status::Failure(_) => Ok(None),
            },
            Err(error) => Err(ModelExtractionError::FailedStatusExtraction(error)),
        }
    }
}

impl Display for FestReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "--- {} ---", self.problem.name)?;
        writeln!(f)?;

        match self.status() {
            Ok(status) => writeln!(f, "status: {status}")?,
            Err(error) => writeln!(f, "error: {error}")?,
        }
        writeln!(f)?;

        writeln!(f, "model:")?;
        match self.model() {
            Ok(result) => match result {
                Some(model) => writeln!(f, "{model}"),
                None => writeln!(f, "none"),
            },
            Err(error) => writeln!(f, "error: {error}"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Fest {
    pub time_limit: usize,
    //pub cores: usize,
}

impl ModelBuilder for Fest {
    type Error = FestError;
    type Report = FestReport;

    // fn cores(&self) -> usize {
    //     if self.cores == 0 { 1 } else { self.cores }
    // }

    fn build(&self, problem: Problem) -> Result<Self::Report, Self::Error> {
        //let start_time = Instant::now();

        let time_limit = self.time_limit.to_string();

        let arguments = Vec::from_iter(["--timeout", &time_limit]);

        // let mut child = Command::new("fest")
        //     .args(arguments)
        //     .stdin(Stdio::piped())
        //     .stdout(Stdio::piped())
        //     .stderr(Stdio::piped())
        //     .spawn()
        //     .map_err(FestError::Spawn)?;

        // let mut stdin = child.stdin.take().unwrap();
        // write!(stdin, "{problem}").map_err(FestError::Write)?;
        // drop(stdin);

        // let output = child
        //     .wait_with_output()
        //     .map_err(FestError::Wait)?
        //     .try_into()?;

        let child = Command::new("fest").arg("countermodel.smt2").status().map_err(FestError::Spawn)?;

        let output = FestOutput { stdout: String::new(), stderr: String::new() };

        Ok(FestReport {
            problem,
            output,
            //elapsed_time: start_time.elapsed(),
        })
    }
}
