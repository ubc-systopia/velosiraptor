use chrono::prelude::*;
use indicatif::{ProgressBar, ProgressStyle};
use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::rc::Rc;
use std::time::Instant;

use velosiast::{
    AstResult, VelosiAst, VelosiAstField, VelosiAstUnit, VelosiAstUnitEnum, VelosiAstUnitSegment,
};
use velosisynth::{SynthOpts, Z3SynthEnum, Z3SynthSegment, Z3WorkerPool};

mod bench;
use bench::*;

const SPECS: [(&str, &str); 11] = [
    ("examples/simple_translation_table.vrs", "Simple Page Table"),
    ("examples/x86_32_pagetable.vrs", "x86\\_32 Page Table"),
    ("examples/x86_64_pagetable.vrs", "x86\\_64 Page Table"),
    ("examples/mpu.vrs", "Arm MPU"),
    ("examples/xeon_phi_smpt.vrs", "Xeon Phi SMPT"),
    ("examples/simple_segment.vrs", "Simple Segment"),
    ("examples/variable_segment.vrs", "Variable Segment"),
    ("examples/medium.vrs", "Medium Segment"),
    ("examples/assoc_segment.vrs", "Assoc Segment"),
    ("examples/x86_segmentation.vrs", "x86 Segmentation"),
    ("examples/r4700_fixed_page_size.vrs", "R4700 TLB"),
];

fn run_synthesis(
    bar: &ProgressBar,
    z3_workers: &mut Z3WorkerPool,
    vrs_file: &str,
    tag: &str,
    no_tree: bool,
) -> Option<BenchResults> {
    let mut results = BenchResults::new(tag.to_string());

    // start of the benchmark
    let t_start = Instant::now();
    let t_0 = t_start;

    bar.set_message("parse spec");

    // construct the AST for the spec
    let mut ast = match VelosiAst::from_file(vrs_file) {
        AstResult::Ok(ast) => ast,
        AstResult::Issues(ast, _e) => ast,
        AstResult::Err(e) => {
            println!("   - ERROR: Spec had errors {vrs_file}\n {e}");
            return None;
        }
    };
    let t_1 = Instant::now();
    results.t_parse.push(t_1.duration_since(t_0).as_millis());

    bar.set_message("create model");

    // create the models
    let t_0 = t_1;
    let models = velosisynth::create_models(&ast);
    let t_1 = Instant::now();
    results.t_model.push(t_1.duration_since(t_0).as_millis());

    let mut num_segments = 0;
    let mut num_staticmaps = 0;
    let mut num_enums = 0;
    let mut total_fields = 0;
    let mut total_slices = 0;
    let mut t_sanity_check = 0;
    let mut t_synth = 0;
    let mut t_finalize = 0;
    let mut n_queries = 0;
    let mut n_cached_queries = 0;
    let mut map_len = 0;
    let mut unmap_len = 0;
    let mut protect_len = 0;
    // let mut t_solver = 0;

    for unit in ast.units_mut() {
        if unit.is_abstract() {
            continue;
        }

        match unit {
            VelosiAstUnit::Segment(u) => {
                num_segments += 1;

                bar.set_message(format!("synthesize {}", u.ident()));

                // println!("Unit: {}", u.ident());

                total_fields += u.interface.fields().len();
                total_slices += u
                    .interface
                    .fields()
                    .iter()
                    .map(|f| f.layout().len())
                    .sum::<usize>();

                // obtain the mutable reference to the segment
                let seg: &mut VelosiAstUnitSegment =
                    Rc::get_mut(u).expect("could not get mut ref!");

                // z3_workers.reset();

                let mut opts = SynthOpts::new();
                opts.disable_tree_opt = no_tree;

                let mut synth =
                    Z3SynthSegment::with_opts(seg, models[seg.ident()].clone(), opts, z3_workers);

                let t_0 = Instant::now();
                // run sanity check
                let sanity_check = synth.sanity_check();
                if let Err(_e) = sanity_check {
                    println!("   - ERROR: Sanity Check failed {}", seg.ident());
                    return None;
                }
                let t_1 = Instant::now();
                t_sanity_check += t_1.duration_since(t_0).as_millis();

                let t_0 = t_1;
                synth.synthesize(false);
                let t_1 = Instant::now();
                t_synth += t_1.duration_since(t_0).as_millis();
                let t_0 = t_1;

                let stats = synth.worker_pool_stats();

                n_queries += stats.n_queries;
                n_cached_queries += stats.n_cached;
                // t_solver += stats.t_solver_ms;

                match synth.finalize() {
                    Ok(r) => {
                        // println!("progs: {r} {} {} {}", r.map_len(), r.protect_len(), r.unmap_len());
                        map_len += r.map_len();
                        unmap_len += r.unmap_len();
                        protect_len += r.protect_len();
                    }
                    Err(_e) => {
                        println!("   - ERROR: Synthesis failed {}", seg.ident());
                        return None;
                    }
                }

                let t_1 = Instant::now();
                t_finalize += t_1.duration_since(t_0).as_millis();
            }
            VelosiAstUnit::StaticMap(_s) => {
                num_staticmaps += 1;
            }
            VelosiAstUnit::Enum(e) => {
                num_enums += 1;

                bar.set_message(format!("distinguish {}", e.ident()));

                let e: &mut VelosiAstUnitEnum = Rc::get_mut(e).expect("could not get mut ref!");

                let t_0 = Instant::now();

                // create the synthesizer from the factory
                let mut synth = Z3SynthEnum::new(z3_workers, e);

                if synth.distinguish(&models).is_err() {
                    println!(
                        "   - ERROR: Could not distinguish models for segment {}",
                        e.ident()
                    );
                    return None;
                }

                let stats = synth.worker_pool_stats();

                n_queries += stats.n_queries;
                n_cached_queries += stats.n_cached;

                let t_1 = Instant::now();
                t_sanity_check += t_1.duration_since(t_0).as_millis();
            }
            _ => { /* no op */ }
        }
    }

    let t_total = Instant::now().duration_since(t_start).as_millis();
    results.t_synth.push(t_synth);
    results.t_check.push(t_sanity_check);
    results.t_total.push(t_total);
    results.t_finalize.push(t_finalize);
    results.n_cached.push(n_cached_queries.try_into().unwrap());
    results.n_queries.push(n_queries.try_into().unwrap());
    results.num_enums = num_enums;
    results.num_staticmaps = num_staticmaps;
    results.num_segments = num_segments;
    results.num_units = num_enums + num_staticmaps + num_segments;
    results.num_fields = total_fields;
    results.num_slices = total_slices;
    results.map_len = map_len;
    results.unmap_len = unmap_len;
    results.protect_len = protect_len;

    // println!("{t_total}ms  {t_solver}ms  {n_queries}q");
    // _ = std::io::stdout().flush();

    Some(results)
}

const LINUX_GIT_URL: &str =
    "https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble";
const LINUX_GIT_SHA: &str = "74134bfb6b720ca18a73931662cbcc8170ef1bed";

fn compile_linux(nworkers: usize, iterations: usize) -> Option<Stats> {
    println!("Running Linux Compilation Benchmark");

    let config_file = Path::new(file!()).parent().unwrap().join("ubuntu.config");
    if !config_file.is_file() {
        println!(
            "ERROR: could not find the config file {}",
            config_file.display()
        );
        return None;
    }

    let tmpdir = env!("CARGO_TARGET_TMPDIR");
    println!(" - Using tmpdir: {tmpdir}");

    let path = Path::new(tmpdir).join("ubuntu2404");
    if let Err(e) = std::fs::create_dir_all(&path) {
        println!("ERROR: Could not create the directory for the linux kernel compilation");
        println!("{e}");
        return None;
    };

    let do_checkout = if !path.join(".git").is_dir() {
        println!(" - Git Init with {LINUX_GIT_URL} ");
        // do a shallow git checkout with git init && git remote add && git fetch && git checkout
        Command::new("git")
            .args(["init"])
            .current_dir(&path)
            .output()
            .expect("failed to execute process");

        Command::new("git")
            .args(["remote", "add", "origin", LINUX_GIT_URL])
            .current_dir(&path)
            .output()
            .expect("failed to execute process");

        true
    } else {
        let output = Command::new("git")
            .args(["rev-parse", "--verify", "HEAD"])
            .current_dir(&path)
            .output()
            .expect("failed to execute process");

        let outstring = String::from_utf8(output.stdout).unwrap();
        if outstring.starts_with(LINUX_GIT_SHA) {
            false
        } else {
            true
        }
    };

    if do_checkout {
        println!(" - Git Checkout {LINUX_GIT_SHA}");
        Command::new("git")
            .args(["fetch", "--depth", "1", "origin", LINUX_GIT_SHA])
            .current_dir(&path)
            .output()
            .expect("failed to execute process");

        Command::new("git")
            .args(["checkout", "FETCH_HEAD"])
            .current_dir(&path)
            .output()
            .expect("failed to execute process");
    }

    // copy the config file
    std::fs::copy(config_file, path.join(".config")).expect("could not copy the config file");

    println!(" - Running make oldconfig");
    // create the new config path
    Command::new("make")
        .args(["oldconfig"])
        .current_dir(&path)
        .output()
        .expect("failed to execute process");

    let bar = ProgressBar::new(iterations.try_into().unwrap());
    bar.set_style(
        ProgressStyle::with_template(
            "{spinner:.dim.bold} [{bar:40.cyan/blue}]  {pos}/{len}  -  {msg:20}",
        )
        .unwrap()
        .tick_chars("/|\\- "),
    );

    let parallelism = format!("-j{}", nworkers);
    let mut measurements = Vec::with_capacity(iterations);
    for _ in 0..iterations {
        bar.set_message("make clean");
        // println!(" - Running make clean");
        Command::new("make")
            .args(["clean"])
            .current_dir(&path)
            .output()
            .expect("failed to execute process");

        bar.set_message("make vmlinux");
        // println!(" - Running make vmlinux");
        let t_start = Instant::now();
        Command::new("make")
            .args(["vmlinux", parallelism.as_str()])
            .current_dir(&path)
            .output()
            .expect("failed to execute process");
        let t_end = Instant::now();

        measurements.push(t_end.duration_since(t_start).as_millis());
        bar.inc(1);
    }

    bar.finish();

    Some(Stats::from(measurements.as_slice()))
}

fn main() {
    println!("# Running Benchmark: Synthesis times\n");

    let nthreads: usize = std::thread::available_parallelism()
        .map(|e| e.into())
        .unwrap_or_else(|_| 1);

    let args: Vec<String> = env::args().collect();

    let output = Command::new("git")
        .args(["status", "--porcelain"])
        .output()
        .expect("failed to execute process");

    let is_dirty = !output.stdout.is_empty();
    let build_dirty = env!("VERGEN_GIT_DIRTY") == "true";
    let allow_dirty = args.iter().any(|e| e.as_str() == "--allow-dirty");
    let is_smoke = args.iter().any(|e| e.as_str() == "--smoke");

    if is_dirty && !allow_dirty {
        println!("ERROR. Git repository is dirty. Terminating.");
        println!("(pass --allow-dirty to ignore)");
        std::process::exit(-1);
    }

    if build_dirty && !allow_dirty {
        println!("ERROR. Executable has been built from a dirty git repository. Terminating.");
        println!("(pass --allow-dirty to ignore)");
        std::process::exit(-1);
    }

    let mut latex_results = String::new();
    let mut latex_results_no_tree = String::new();

    let nworkers =  if nthreads > 1 { (nthreads / 2) - 1 } else { 1 };
    let iterations = if is_smoke { 5 } else { ITERATIONS };
    for (spec, name) in SPECS.iter() {
        println!(" @ Spec: {spec}");

        let vrs = PathBuf::from(spec);
        let vrs_file = vrs.display().to_string();
        if !vrs.is_file() {
            println!("   - ERROR: Spec not found: {spec}");
            continue;
        }

        for no_tree in &[false] {
            //for no_tree in &[true, false] {

            let name = if *no_tree {
                format!("{name} (no tree)")
            } else {
                name.to_string()
            };
            let mut results = BenchResults::new(name.to_string());
            let mut had_errors = false;
            print!("    ");
            let bar = ProgressBar::new(iterations.try_into().unwrap());
            bar.set_style(
                ProgressStyle::with_template(
                    "{spinner:.dim.bold} [{bar:40.cyan/blue}]  {pos}/{len}  -  {msg:20}",
                )
                .unwrap()
                .tick_chars("/|\\- "),
            );

            for _ in 0..iterations {
                // create synth factory and run synthesis on the segments
                let mut z3_workers = Z3WorkerPool::with_num_workers(nworkers, None);
                if let Some(res) = run_synthesis(
                    &bar,
                    &mut z3_workers,
                    vrs_file.as_str(),
                    name.as_str(),
                    *no_tree,
                ) {
                    results.merge(&res);
                } else {
                    had_errors = true;
                    break;
                }

                z3_workers.terminate();
                bar.inc(1);
            }
            bar.finish();

            if had_errors {
                break;
            }

            print!("  - {results}\n");

            let res = if *no_tree {
                &mut latex_results_no_tree
            } else {
                &mut latex_results
            };

            if res.is_empty() {
                let hdr = format!(
                    "  {:<20} & {:<11}          & {:<11} & {:12} & {:12} \\\\\n",
                    "Name", "\\# Units", " Programs ", "  Time P50", "  Time P95"
                );

                res.push_str(hdr.as_str());
                res.push_str("  \\hline % ---------------------------------------------------------------------------------\n");
            }

            res.push_str("  ");
            res.push_str(results.to_latex().as_str());
        }
    }
    latex_results.push_str("  \\hline % ---------------------------------------------------------------------------------");

    let linux_times = compile_linux(nthreads, iterations);

    println!("# Completed\n\n");

    let dirty = if is_dirty || build_dirty {
        "-dirty"
    } else {
        ""
    };

    println!(
        "% =========================================================================================="
    );
    println!("% Table: Synthesis Times");
    println!(
        "% =========================================================================================="
    );
    println!("% Git Hash:   {}{dirty}", env!("VERGEN_GIT_DESCRIBE"));
    println!("% CPU:        {}", env!("VERGEN_SYSINFO_CPU_BRAND"));
    println!("% OS:         {}", env!("VERGEN_SYSINFO_OS_VERSION"));
    println!("% Date:       {}", Local::now());
    println!("% Threads:    {}", nthreads);
    println!("% Workers:    {}", nworkers);
    println!("% Iterations: {}", iterations);
    println!(
        "% =========================================================================================="
    );
    println!("%");
    println!("\\begin{{tabular}}{{lc|crr}}");
    println!("  \\hline % ---------------------------------------------------------------------------------");
    println!("  \\multicolumn{{2}}{{c}}{{\\textbf{{Configurations}}}} & \\multicolumn{{3}}{{c}}{{\\textbf{{Results [ms]}}}} \\\\");
    println!("{latex_results}");
    if let Some(linux_measurement) = linux_times {
        println!("  Linux Ubuntu         &                  --  & --          & {:>9}ms  & {:>9}ms  \\\\",
        BenchResults::human_readable(linux_measurement.med),
        BenchResults::human_readable(linux_measurement.p95));
    } else {
        println!(
            "  Linux Ubuntu         &                  --  & --          & N/A ms & N/A ms \\\\"
        );
    }
    println!("  \\hline % ---------------------------------------------------------------------------------");
    println!("\\end{{tabular}}");
    println!("%");
    println!(
        "% =========================================================================================="
    );
    //println!("% latex table\n{latex_results_no_tree}");
}
