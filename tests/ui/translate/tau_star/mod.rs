use {assert_cmd::Command, std::path::Path};

#[test]
fn translate_examples() {
    for example in Path::new(file!())
        .parent()
        .unwrap()
        .join("examples")
        .read_dir()
        .unwrap()
        .map(Result::unwrap)
        .filter(|entry| entry.metadata().unwrap().is_dir())
        .map(|entry| entry.path())
    {
        let program = example.join("program.lp");
        let stdout = example.join("stdout");
        let stderr = example.join("stderr");

        let mut cmd = Command::cargo_bin(env!("CARGO_PKG_NAME")).unwrap();
        let assert = cmd
            .arg("translate")
            .arg("--with")
            .arg("tau-star")
            .arg("--dialect=gringo-five")
            .arg(program)
            .assert();

        assert
            .stdout(std::fs::read_to_string(stdout).unwrap())
            .stderr(std::fs::read_to_string(stderr).unwrap());
    }
}
