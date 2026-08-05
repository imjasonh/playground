fn main() {
    // GIT_SHA stays in env! — it's not a secret and is useful in the
    // boot summary log line for identifying which build is running.
    // Wi-Fi creds, trust config, and (future) GCP creds all come from
    // NVS now (see provisioning-plan.md).
    println!("cargo:rerun-if-env-changed=GIT_SHA");
    embuild::espidf::sysenv::output();
}
