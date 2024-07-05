use std::path::PathBuf;
use std::rc::Rc;
use std::time::Instant;

use velosiast::{
    AstResult, VelosiAst, VelosiAstField, VelosiAstUnit, VelosiAstUnitEnum, VelosiAstUnitSegment,
};
use velosisynth::{SynthOpts, Z3SynthEnum, Z3SynthSegment, Z3WorkerPool};

mod bench;
use bench::*;

const SPECS: [(&str, &str); 10] = [
    ("examples/simple_translation_table.vrs", "Simple Page Table"),
    ("examples/x86_32_pagetable.vrs", "x86\\_32 Page Table"),
    ("examples/x86_64_pagetable.vrs", "x86\\_64 Page Table"),
    ("examples/xeon_phi_smpt.vrs", "Xeon Phi SMPT"),
    ("examples/simple_segment.vrs", "Simple Segment"),
    ("examples/variable_segment.vrs", "Variable Segment"),
    ("examples/medium.vrs", "Medium Segment"),
    ("examples/assoc_segment.vrs", "Assoc Segment"),
    ("examples/x86_segmentation.vrs", "x86 Segmentation"),
    ("examples/r4700_fixed_page_size.vrs", "R4700 TLB"),
];

fn run_synthesis(
    z3_workers: &mut Z3WorkerPool,
    vrs_file: &str,
    tag: &str,
    no_tree: bool,
) -> Option<BenchResults> {
    let mut results = BenchResults::new(tag.to_string());

    // start of the benchmark
    let t_start = Instant::now();
    let t_0 = t_start;

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

fn main() {
    println!("# Running Benchmark: Synthesis times");

    let mut latex_results = String::new();
    let mut latex_results_no_tree = String::new();

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
            for _ in 0..ITERATIONS {
                // create synth factory and run synthesis on the segments
                let mut z3_workers = Z3WorkerPool::with_num_workers(NUM_WORKERS, None);
                if let Some(res) =
                    run_synthesis(&mut z3_workers, vrs_file.as_str(), name.as_str(), *no_tree)
                {
                    results.merge(&res);
                } else {
                    had_errors = true;
                    break;
                }

                z3_workers.terminate();
            }
            println!("");

            if had_errors {
                break;
            }

            print!("  - {results}\n");

            if *no_tree {
                if latex_results_no_tree.is_empty() {
                    latex_results_no_tree.push_str(results.to_latex_header().as_str());
                }

                latex_results_no_tree.push_str(results.to_latex().as_str());
            } else {
                if latex_results.is_empty() {
                    latex_results.push_str(results.to_latex_header().as_str());
                }
                latex_results.push_str(results.to_latex().as_str());
            }
        }
    }

    println!("# Completed");

    println!("% latex table\n{latex_results}");

    println!("% latex table\n{latex_results_no_tree}");

}
