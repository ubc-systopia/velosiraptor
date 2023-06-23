pub fn with_prefix(prefix: &str, identifier: &str) -> String {
    format!("{prefix}.{identifier}")
}
