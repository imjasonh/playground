fn main() {
    println!("cargo:rerun-if-env-changed=GIT_SHA");
    if std::env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("espidf") {
        embuild::espidf::sysenv::output();
    }
}
