use vergen::EmitBuilder;
use anyhow::Result;

pub fn main() -> Result<()> {
    // NOTE: This will output only a build timestamp and long SHA from git.
    // NOTE: This set requires the build and git features.
    // NOTE: See the EmitBuilder documentation for configuration options.
    EmitBuilder::builder()
        .all_build()
        .all_git()
        .all_sysinfo()
        .emit()?;
    Ok(())
}