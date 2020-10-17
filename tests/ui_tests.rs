use compiletest_rs::{run_tests, Config};

#[test]
pub fn run_ui_tests() {
    let mut config = Config {
        mode: "ui".parse().unwrap(),
        src_base: "tests/ui".into(),
        build_base: "target/debug/ui_tests".into(),
        ..Config::default()
    };
    config.link_deps();
    config.clean_rmeta();
    run_tests(&config);
}
