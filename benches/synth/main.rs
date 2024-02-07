use std::path::PathBuf;
use std::rc::Rc;
use std::time::Instant;

use velosiast::{
    AstResult, VelosiAst, VelosiAstField, VelosiAstUnit, VelosiAstUnitEnum, VelosiAstUnitSegment,
};
use velosisynth::{Z3SynthEnum, Z3SynthSegment, Z3WorkerPool};

const SPECS: [&str; 7] = [
    "examples/x86_32_pagetable.vrs",
    "examples/x86_64_pagetable.vrs",
    "examples/xeon_phi_smpt.vrs",
    "examples/singlesegment.vrs",
    "examples/medium.vrs",
    "examples/fixedsegment.vrs",
    "examples/r4700_fixed_page_size.vrs",
];

const NUM_WORKERS: usize = 13;
const ITERATIONS: usize = 10;

struct Stats {
    pub min: u128,
    pub med: u128,
    pub avg: u128,
    pub max: u128,
    pub var: u128,
    pub std: u128,
    pub num: usize,
}

impl From<&[u128]> for Stats {
    fn from(stats: &[u128]) -> Self {
        let mut data = stats.to_vec();

        let sum = data.iter().sum::<u128>() as u128;
        let num = data.len();
        let avg = sum / num as u128;

        if num == 0 {
            Self {
                min: 0,
                med: 0,
                avg: 0,
                max: 0,
                var: 0,
                std: 0,
                num: 0,
            }
        } else {
            data.sort();
            let var =
                data.iter().map(|x| (x - avg) * (x - avg)).sum::<u128>() as u128 / num as u128;
            let std = (var as f64).sqrt() as u128;
            Self {
                min: *data.first().unwrap(),
                med: data[num / 2],
                avg,
                max: *data.last().unwrap(),
                var,
                std,
                num,
            }
        }
    }
}

struct BenchResults {
    pub tag: String,
    pub t_parse: Vec<u128>,
    pub t_model: Vec<u128>,
    pub t_check: Vec<u128>,
    pub t_synth: Vec<u128>,
    pub t_finalize: Vec<u128>,
    pub t_total: Vec<u128>,
    pub num_segments: usize,
    pub num_staticmaps: usize,
    pub num_enums: usize,
    pub num_units: usize,
    pub num_fields: usize,
    pub num_slices: usize,
}

impl BenchResults {
    pub fn new(tag: String) -> Self {
        Self {
            tag,
            t_parse: Vec::new(),
            t_model: Vec::new(),
            t_check: Vec::new(),
            t_synth: Vec::new(),
            t_total: Vec::new(),
            t_finalize: Vec::new(),
            num_segments: 0,
            num_staticmaps: 0,
            num_enums: 0,
            num_units: 0,
            num_fields: 0,
            num_slices: 0,
        }
    }

    pub fn merge(&mut self, other: &Self) {
        assert_eq!(self.tag, other.tag);
        self.t_parse.extend(other.t_parse.iter());
        self.t_model.extend(other.t_model.iter());
        self.t_check.extend(other.t_check.iter());
        self.t_synth.extend(other.t_synth.iter());
        self.t_total.extend(other.t_total.iter());
        self.t_finalize.extend(other.t_finalize.iter());
        if self.num_segments == 0 {
            self.num_segments = other.num_segments;
        } else {
            assert_eq!(self.num_segments, other.num_segments);
        }
        if self.num_staticmaps == 0 {
            self.num_staticmaps = other.num_staticmaps;
        } else {
            assert_eq!(self.num_staticmaps, other.num_staticmaps);
        }
        if self.num_enums == 0 {
            self.num_enums = other.num_enums;
        } else {
            assert_eq!(self.num_enums, other.num_enums);
        }
        if self.num_units == 0 {
            self.num_units = other.num_units;
        } else {
            assert_eq!(self.num_units, other.num_units);
        }
        if self.num_fields == 0 {
            self.num_fields = other.num_fields;
        } else {
            assert_eq!(self.num_fields, other.num_fields);
        }
        if self.num_slices == 0 {
            self.num_slices = other.num_slices;
        } else {
            assert_eq!(self.num_slices, other.num_slices);
        }
    }
}

impl std::fmt::Display for BenchResults {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let tt = Stats::from(self.t_total.as_slice());
        let tc = Stats::from(self.t_check.as_slice());
        let ts = Stats::from(self.t_synth.as_slice());
        let tp = Stats::from(self.t_parse.as_slice());

        write!(f, "{:<30} {:2}+{:2}+{:2}  {:4}    {:10}ms (+/- {:4})  synth: {:10}ms (+/- {:4})  check:  {:4}ms (+/- {:2})  parse:  {:4}ms (+/- {:2})",
            self.tag, self.num_units, self.num_fields, self.num_slices, ts.num, tt.avg, tt.std, ts.avg, ts.std, tc.avg, tc.std,
            tp.avg, tp.std
        )?;

        Ok(())
    }
}

fn run_synthesis(z3_workers: &mut Z3WorkerPool, vrs_file: &str) -> Option<BenchResults> {
    let mut results = BenchResults::new(vrs_file.to_string());

    // start of the benchmark
    let t_start = Instant::now();
    let t_0 = t_start;

    // construct the AST for the spec
    let mut ast = match VelosiAst::from_file(vrs_file) {
        AstResult::Ok(ast) => ast,
        AstResult::Issues(ast, _e) => ast,
        AstResult::Err(_e) => {
            println!("   - ERROR: Spec had errors {vrs_file}");
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

    for unit in ast.units_mut() {
        if unit.is_abstract() {
            continue;
        }

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

                let t_0 = Instant::now();

                // obtain the mutable reference to the segment
                let seg: &mut VelosiAstUnitSegment =
                    Rc::get_mut(u).expect("could not get mut ref!");

                // z3_workers.reset();

                // create the synthesizer from the factory
                let mut synth = Z3SynthSegment::new(z3_workers, seg, models[seg.ident()].clone());
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

                match synth.finalize() {
                    Ok(_r) => {
                        // println!("{}{r}", seg.ident());
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
    results.num_enums = num_enums;
    results.num_staticmaps = num_staticmaps;
    results.num_segments = num_segments;
    results.num_units = num_enums + num_staticmaps + num_segments;
    results.num_fields = total_fields;
    results.num_slices = total_slices;

    Some(results)
}

fn main() {
    println!("# Running Benchmark: Synthesis times");

    for spec in SPECS.iter() {
        println!(" @ Spec: {spec}");

        let vrs = PathBuf::from(spec);
        let vrs_file = vrs.display().to_string();
        if !vrs.is_file() {
            println!("   - ERROR: Spec not found: {spec}");
            continue;
        }

        let mut results = BenchResults::new(vrs_file.clone());
        let mut had_errors = false;
        for _ in 0..ITERATIONS {
            // create synth factory and run synthesis on the segments
            let mut z3_workers = Z3WorkerPool::with_num_workers(NUM_WORKERS, None);
            if let Some(res) = run_synthesis(&mut z3_workers, vrs_file.as_str()) {
                results.merge(&res);
            } else {
                had_errors = true;
                break;
            }

            z3_workers.terminate();
        }

        if had_errors {
            break;
        }

        println!("{results}");
    }

    println!("# Completed");
}
