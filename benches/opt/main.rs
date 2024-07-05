use std::collections::HashMap;
use std::path::PathBuf;
use std::rc::Rc;
use std::time::Instant;

use velosiast::{
    AstResult, VelosiAst, VelosiAstField, VelosiAstUnit, VelosiAstUnitSegment,
};
use velosisynth::{SynthOpts, Z3SynthSegment, Z3WorkerPool};

const SPECS: [(&str, &str); 10] = [
    ("examples/simple_translation_table.vrs", "Simple Page Table"),
    ("examples/x86_32_pagetable.vrs", "x86\\_32 Page Table"),
    ("examples/x86_64_pagetable.vrs", "x86\\_64 Page Table"),
    ("examples/xeon_phi_smpt.vrs", "Xeon Phi SMPT"),
    ("examples/simple_segment.vrs", "Simple Segment"),
    ("examples/variable_segment.vrs", "Variable Segment"),
    ("examples/medium.vrs", "Medium Segment"),
    ("examples/x86_segmentation.vrs", "x86 Segmentation"),
    ("examples/assoc_segment.vrs", "Assoc Segment"),
    ("examples/r4700_fixed_page_size.vrs", "R4700 TLB"),
];

const OPTS: [(&str, (bool, bool, bool, bool, bool)); 5] = [
    //               iface  state  expr   cache   tree
    ("No Opts", (true, true, true, true, true)),
    ("+ IfaceOpt", (false, true, true, true, true)),
    ("+ StateOpt", (false, false, true, true, true)),
    ("+ ExprOpt", (false, false, false, true, true)),
    ("+ Tree", (false, false, false, true, false)),
    // ("+ Cache (full)", (false, false, false, false, false)),
];

mod bench;
use bench::*;

fn run_synthesis(
    z3_workers: &mut Z3WorkerPool,
    vrs_file: &str,
    tag: String,
    myopts: &(bool, bool, bool, bool, bool),
) -> Option<BenchResults> {
    let mut results = BenchResults::new(tag);

    // start of the benchmark
    let t_start = Instant::now();
    let _t_0 = t_start;

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

    // create the models
    let _t_0 = t_1;
    let models = velosisynth::create_models(&ast);
    let _t_1 = Instant::now();

    let mut num_segments = 0;
    let mut num_staticmaps = 0;
    let mut num_enums = 0;
    let mut total_fields = 0;
    let mut total_slices = 0;
    let n_queries = 0;
    let n_cached_queries = 0;
    let mut n_programs = 0;
    let mut n_programs_max = None;

    let _map_len = 0;
    let _unmap_len = 0;
    let _protect_len = 0;

    for unit in ast.units_mut() {
        if unit.is_abstract() {
            continue;
        }

        let mut opts = SynthOpts::new();
        opts.disable_iface_opt = myopts.0;
        opts.disable_state_opt = myopts.1;
        opts.disable_expr_opt = myopts.2;
        opts.disable_cache_opt = myopts.3;
        opts.disable_tree_opt = myopts.4;
        opts.disable_program_generation = true;

        z3_workers.disable_query_cache(opts.disable_cache_opt);

        match unit {
            VelosiAstUnit::Segment(u) => {
                num_segments += 1;

                total_fields += u.interface.fields().len();
                total_slices += u
                    .interface
                    .fields()
                    .iter()
                    .map(|f| f.layout().len())
                    .sum::<usize>();

                let _t_0 = Instant::now();

                // obtain the mutable reference to the segment
                let seg: &mut VelosiAstUnitSegment =
                    Rc::get_mut(u).expect("could not get mut ref!");
                // create the synthesizer from the factory
                let synth =
                    Z3SynthSegment::with_opts(seg, models[seg.ident()].clone(), opts, z3_workers);

                let (n_progs, n_progs_max) = synth.num_programs();

                n_programs += n_progs;
                n_programs_max = if let Some(n) = n_programs_max {
                    Some(n + n_progs_max.unwrap_or_default())
                } else {
                    n_progs_max
                };
            }
            VelosiAstUnit::StaticMap(_s) => {
                num_staticmaps += 1;
            }
            VelosiAstUnit::Enum(_e) => {
                num_enums += 1;
            }
            _ => { /* no op */ }
        }
    }

    let _t_total = Instant::now().duration_since(t_start).as_millis();
    results.n_cached.push(n_cached_queries.try_into().unwrap());
    results.n_queries.push(n_queries.try_into().unwrap());
    results.num_enums = num_enums;
    results.num_staticmaps = num_staticmaps;
    results.num_segments = num_segments;
    results.num_units = num_enums + num_staticmaps + num_segments;
    results.num_fields = total_fields;
    results.num_slices = total_slices;
    results.n_programs = n_programs;
    results.n_programs_max = n_programs_max;

    Some(results)
}

fn main() {
    println!("# Running Benchmark: Synthesis Optimizations");

    let mut latex_results = String::new();

    latex_results.push_str("Spec");

    for (_i, (tag, _)) in OPTS.iter().enumerate() {
        latex_results.push_str(" & ");
        latex_results.push_str(tag);
    }
    latex_results.push_str("\\\\\n");
    latex_results.push_str("\\hline\n");

    for (spec, name) in SPECS.iter() {
        println!(" @ Spec: {spec}");
        let mut row = HashMap::new();
        for (mytag, opts) in OPTS.iter() {
            println!("   - Opt: {mytag}");

            let vrs = PathBuf::from(spec);
            let vrs_file = vrs.display().to_string();
            if !vrs.is_file() {
                println!("   - ERROR: Spec not found: {spec}");
                continue;
            }

            let tag = format!("{name}{mytag}");

            let mut results = BenchResults::new(tag.clone());

            // create synth factory and run synthesis on the segments
            let mut z3_workers = Z3WorkerPool::with_num_workers(NUM_WORKERS, None);
            if let Some(res) = run_synthesis(&mut z3_workers, vrs_file.as_str(), tag.clone(), opts)
            {
                results.merge(&res);
            } else {
                break;
            }

            z3_workers.terminate();

            row.insert(mytag, results.n_programs_max.unwrap_or_default());
        }

        latex_results.push_str(format!("{name:20}").as_str());
        latex_results.push_str(" & ");
        for (i, (tag, _)) in OPTS.iter().enumerate() {
            if i > 0 {
                latex_results.push_str(" & ");
            }
            let num = row.get(tag).unwrap().ilog10();

            latex_results.push_str(&format!("{num:3}"));
        }
        latex_results.push_str("\\\\\n");

    }
    latex_results.push_str("\\hline\n");
    println!("# Completed");

    println!("% latex table\n{latex_results}");
}
