// VelosiRaptor FastModels Tests
//
//
// MIT License
//
// Copyright (c) 2023 Systopia Lab, Computer Science, University of British Columbia
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

use std::path::{Path, PathBuf};
use std::fs;

use std::process::Command;

use velosihwgen::VelosiHwGen;
use velosiast::{AstResult, VelosiAst};

use rexpect::{process::signal::SIGKILL, reader::{Regex, ReadUntil}, session::PtyReplSession, spawn_bash};

/// Test the hardware generation
#[test]
fn examples_hwgen_fastmodels() {
    let d = PathBuf::from("examples");
    let outdir = Path::new("out/examples_hwgen_fastmodels");
    for f in d.read_dir().expect("could not read example directory") {
        let vrs = f.expect("could not read directory entry").path();

        if vrs.is_dir() {
            continue;
        }

        generate_and_check(&vrs, &outdir);
    }
}

/// Test the
#[test]
// #[ignore]
fn example_direct_segment_fastmodels() {
    let mut vrs = PathBuf::from("examples");
    vrs.push("directsegment.vrs");
    assert!(vrs.is_file());

    let outdir = Path::new("out/example_direct_segment_fastmodels");

    generate_and_check(&vrs, &outdir);
    build_fastmodels(&vrs, &outdir);
    build_bootimg(&vrs, &outdir);
    run_fastmodels(&vrs, &outdir);
}

/// Test the
#[test]
#[ignore]
fn example_simple_translation_table_fastmodels() {
    let mut vrs = PathBuf::from("examples");
    vrs.push("simple_translation_table.vrs");
    assert!(vrs.is_file());

    let outdir = Path::new("out/example_simple_translation_table_fastmodels");

    generate_and_check(&vrs, &outdir);
}

/// Test the
#[test]
#[ignore]
fn example_x86_32_pagetable_table_fastmodels() {
    let mut vrs = PathBuf::from("examples");
    vrs.push("x86_32_pagetable.vrs");
    assert!(vrs.is_file());

    let outdir = Path::new("out/example_x86_32_pagetable_table_fastmodels");

    generate_and_check(&vrs, &outdir);
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Test Utils for the FastModels HW Gen
////////////////////////////////////////////////////////////////////////////////////////////////////

fn get_fastmodels_path() -> PathBuf {
    let homedir = std::env::home_dir().expect("could not get the home directory");
    homedir.join("bin/arm/FastModelsTools_11.15")
}

/// builds the fastmodels emulated system
#[cfg(test)]
fn generate_and_check(vrs: &Path, outdir: &Path) {
    assert!(vrs.is_file());

    fs::create_dir_all(outdir).expect("failed to create the output directory");

    let name = vrs.file_stem().unwrap().to_string_lossy();
    let path_str = vrs.to_str().expect("could not create string from path");

    println!("\nGenerate and Check: {path_str}.vrs");

    print!("  - Parsing {:40} ...", name);

    let ast = match VelosiAst::from_file(path_str) {
        AstResult::Ok(ast) => {
            println!(" ok");
            ast
        }
        AstResult::Issues(ast, _e) => {
            println!(" ok  (with issues)");
            // println!(">>>>>>\n{e}\n<<<<<<");
            ast
        }
        AstResult::Err(e) => {
            println!(" fail  (expected ok)");
            println!(">>>>>>\n{e}\n<<<<<<");
            panic!("Failed to construct AST.");
        }
    };

    print!("  - generate hardware module (fast models)... ");

    let hwgen = VelosiHwGen::new_fastmodels(outdir, name.clone().into());
    hwgen
        .prepare()
        .expect("could not prepare the hwgen backend");

    if let Err(e) = hwgen.generate(&ast) {
        println!(" failed!");
        println!(">>>>>>\n{e:?}\n<<<<<<");
    } else {
        println!(" ok");
    }

    hwgen.finalize(&ast).expect("could not finalize");

    print!("  - Compiling hardware module ... ");

    let outpath = outdir
        .join(name.to_string())
        .join("hw/fastmodels");

    // run make
    let make = Command::new("make")
        .arg("unitlib")
        .env("TEST_MOCK_FAST_MODELS", "1")
        .current_dir(outpath)
        .output()
        .expect("Failed to execute command");

    if make.status.success() {
        let errs = String::from_utf8(make.stderr).unwrap();

        if errs.is_empty() {
            println!(" ok");
        } else {
            println!(" ok  (with issues)");
            println!(">>>>>>\n{errs}\n<<<<<<");
            let errs = String::from_utf8(make.stdout).unwrap();
            println!(">>>>>>\n{errs}\n<<<<<<");
            panic!("Compilation resulted in warnings");
        }
    } else {
        println!(" failed. (errors during compilation");
        let errs = String::from_utf8(make.stdout).unwrap();
        println!(">>>>>>\n{errs}\n<<<<<<");

        let errs = String::from_utf8(make.stderr).unwrap();
        println!(">>>>>>\n{errs}\n<<<<<<");

        panic!("Compilation resulted in errors");
    }
}

/// builds the fastmodels emulated system
#[cfg(test)]
fn build_fastmodels(vrs: &Path, outdir: &Path) {
    let name = vrs.file_stem().unwrap().to_string_lossy();
    let path_str = vrs.to_str().expect("could not create string from path");

    println!("\nBuilding FastModels: {path_str}.vrs");

    print!("  - Compiling hardware module ... ");

    let fastmodels_config_file = get_fastmodels_path().join("source_all.sh");

    let outpath = outdir
        .join(name.to_string())
        .join("hw/fastmodels");

    let command_str = format!("source {}; make", fastmodels_config_file.display());

    // run make
    let make = Command::new("bash")
        .args(["-c", command_str.as_str()])
        .current_dir(outpath)
        .output()
        .expect("Failed to execute command");

    if make.status.success() {
        let errs = String::from_utf8(make.stderr).unwrap();

        if errs.is_empty() {
            println!(" ok");
        } else {
            if errs.starts_with("ar: `u' modifier") {
                println!(" ok");
            } else {
                println!(" ok  (with issues)");
                println!(">>>>>>\n{errs}\n<<<<<<");
                let errs = String::from_utf8(make.stdout).unwrap();
                println!(">>>>>>\n{errs}\n<<<<<<");
                panic!("Compilation resulted in warnings");
            }
        }
    } else {
        println!(" failed. (errors during compilation");
        let errs = String::from_utf8(make.stdout).unwrap();
        println!(">>>>>>\n{errs}\n<<<<<<");
        let errs = String::from_utf8(make.stderr).unwrap();
        println!(">>>>>>\n{errs}\n<<<<<<");

        panic!("Compilation resulted in errors");
    }
}


/// builds the boot image
#[cfg(test)]
fn build_bootimg(vrs: &Path, outdir: &Path) {

    println!("\nBuilding Bootimage");

    let bootimg_src = Path::new("support/arm-fastmodels-boot");

    // run make
    let make = Command::new("make")
        .arg("bootimg.bin")
        .current_dir(bootimg_src)
        .output()
        .expect("Failed to execute command");

    if make.status.success() {
        let errs = String::from_utf8(make.stderr).unwrap();

        if errs.is_empty() {
            println!(" ok");
        } else {
            println!(" ok  (with issues)");
            println!(">>>>>>\n{errs}\n<<<<<<");
            let errs = String::from_utf8(make.stdout).unwrap();
            println!(">>>>>>\n{errs}\n<<<<<<");
            panic!("Compilation resulted in warnings");
        }
    } else {
        println!(" failed. (errors during compilation");
        let errs = String::from_utf8(make.stdout).unwrap();
        println!(">>>>>>\n{errs}\n<<<<<<");

        let errs = String::from_utf8(make.stderr).unwrap();
        println!(">>>>>>\n{errs}\n<<<<<<");

        panic!("Compilation resulted in errors");
    }

}

fn expect_output(p: &mut PtyReplSession, output: &mut String, expected: &str) {


    let abort_string = "[ARMv8]: ERROR Exception AARCH64_EVECTOR_EL_CURRENT_STACK_CURRENT_SYNC happened";
    let r = p.exp_any(vec![
        ReadUntil::String(abort_string.into()),
        ReadUntil::Regex(Regex::new(expected).unwrap())]
    );
    let has_err = match r {
        Ok((o, s)) => {
            output.push_str(&o);
            output.push_str(&s);
            if s == abort_string {
                println!("Translation resulted in an excepction.");
                println!("Recognized abort string: `{}`", abort_string);
                println!("{o}");
                true
            } else {
                false
            }
        }
        Err(_e) =>  {
            println!("Could not recognize `{expected}`");
            while let Some(c) = p.try_read() {
                output.push(c);
            }

            true
        }
    };

    if has_err {
        let _ = p.send_control('c');
        let _ = p.process.kill(SIGKILL);
        let _ = p.process.wait();
        println!("OUTPUT:");
        for line in output.lines() {
            println!("  > {line}");
        }
        panic!("failure in recognizing expected output");
    }
}

/// runs the fastmodels emulated system
#[cfg(test)]
fn run_fastmodels(vrs: &Path, outdir: &Path) {
    let name = vrs.file_stem().unwrap().to_string_lossy();
    let path_str = vrs.to_str().expect("could not create string from path");

    println!("\nRunning FastModels: {path_str}.vrs");

    let outpath = outdir
        .join(name.to_string())
        .join("hw/fastmodels");

    // set in the makefile
    let simprog = outpath.join("build/plat_example_sim");
    println!("  - sim: {}", simprog.display());
    assert!(simprog.is_file());

    let bootimg_src = Path::new("support/arm-fastmodels-boot");

    let bootimg = bootimg_src.join("bootimg.bin");
    println!("  - bootimg: {}", bootimg.display());
    assert!(bootimg.is_file());

    let fastmodels_config_file = get_fastmodels_path().join("source_all.sh");

    // run make
    let mut p = spawn_bash(Some(5000))
        .expect("could not spawn bash process");

    let command_str = format!("source {}; ./{} --data Memory0={}@0x0", fastmodels_config_file.display(), simprog.display(), bootimg.display());
    // println!("  - cmd: {command_str}");
    p.send_line(command_str.as_str())
        .expect("could not send command to bash");

    let mut output = String::new();

    expect_output(&mut p, &mut output, r"\[UNIT\] \[ WARN\] Initializing translation unit");
    expect_output(&mut p, &mut output, r"\[ARMv8\]: FastModels bootloader starting on ARM Cortex-A53");

    expect_output(&mut p, &mut output, r"\[ARMv8\]: VRS: Velosiraptor tests starting.");
    expect_output(&mut p, &mut output, r"\[ARMv8\]: Velosiraptor tests completed.");


    let _ = p.send_control('c');
    let _ = p.process.kill(SIGKILL);
    let _ = p.process.wait();
}




