use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
mod bench;
use bench::*;

const CONFIGS: [&str; 12] = [
    "Linux-Map",
    "Arbutus-Map",
    "Linux-Protect",
    "Arbutus-Protect",
    "Linux-Unmap",
    "Arbutus-Unmap",
    "Barrelfish-Kernel-Map",
    "Arbutus-PTable-Map",
    "Barrelfish-Kernel-Protect",
    "Arbutus-PTable-Protect",
    "Barrelfish-Kernel-Unmap",
    "Arbutus-PTable-Unmap",
];

const ROWS: [&str; 4] = [
    "Linux-x86_64",
    "Arbutus-x86_64",
    "Barrelfish-PTable",
    "Arbutus-PTable",
];

const COLS: [&str; 3] = ["Map", "Protect", "Unmap"];

fn compile_and_run() -> Result<String, ()> {
    let dir = PathBuf::from("benches/runtime");
    println!(" - Compiling benchmark binary...");
    let build = Command::new("make")
        .current_dir(dir.as_path())
        .output()
        .expect("failed to build the benchmark");

    if !build.status.success() {
        println!("Build failed: {}", String::from_utf8_lossy(&build.stdout));
        println!("Build failed: {}", String::from_utf8_lossy(&build.stderr));
        return Err(());
    }

    println!(" - Running benchmark...");
    let run = Command::new("./bench")
        .current_dir(dir.as_path())
        .output()
        .expect("failed to run the benchmark");

    if !run.status.success() {
        println!(
            "    ## Run failed: {}",
            String::from_utf8_lossy(&run.stdout)
        );
        println!(
            "    ## Run failed: {}",
            String::from_utf8_lossy(&run.stderr)
        );
        return Err(());
    }

    Ok(String::from_utf8_lossy(&run.stdout).to_string())
}

struct Measurements {
    measurements: HashMap<String, Stats>,
}

impl Measurements {
    pub fn to_latex(&self) -> String {
        let mut res = String::new();

        res.push_str("\\hline\n");

        res.push_str(&format!("\\th{{{:<10}}}", ""));
        res.push_str(&format!("& \\th{{{:<10}}}", "Operation"));
        for col in &COLS {
            res.push_str(&format!(" & \\span{{\\th{{{:^7}}}}}", col));
        }
        res.push_str(" \\\\\n");
        res.push_str(&format!("\\th{{{:<10}}}", "Structure"));
        res.push_str(&format!("& \\th{{{:<10}}}", "Code"));
        res.push_str(&format!(
            " & \\th{{{}}} & \\th{{{}}} & \\th{{{}}} & \\th{{{}}} & \\th{{{}}} & \\th{{{}}} \\\\\n",
            "P50", "P95", "P50", "P95", "P50", "P95"
        ));
        let mut prev = "";
        for row in &ROWS {
            let mut parts = row.split('-');
            let env = parts.next().unwrap();
            let cfg = parts.next().unwrap();
            if prev != cfg {
                res.push_str("\\hline\n");
                prev = cfg;
            }
            res.push_str(&format!("{:<15}", cfg.replace('_', "\\_")));
            res.push_str(&format!("& {:<15}", env));
            for col in &COLS {
                let key = format!("{}-{}", row, col);
                if let Some(v) = self.measurements.get(&key) {
                    res.push_str(&format!(" & {:6}ns & {:6}ns", v.med, v.p95));
                } else {
                    res.push_str(&format!(" & {:6}ns & {:6}ns", "??", "??"));
                }
            }
            res.push_str(" \\\\\n");
        }
        res.push_str("\\hline\n");

        return res;
    }
}

impl std::fmt::Display for Measurements {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for c in &CONFIGS {
            if let Some(v) = self.measurements.get(*c) {
                write!(
                    f,
                    "{:<30}  {:6}ns {:6}ns {:6}ns ({})\n",
                    c, v.avg, v.med, v.p99, v.num
                )?;
            } else {
                write!(
                    f,
                    "{:<30}  {:6}ns {:6}ns {:6}ns ({})\n",
                    c, "??", "??", "??", "??"
                )?;
            }
        }
        Ok(())
    }
}

fn parse_results(output: &str) -> Measurements {
    let mut measurements = HashMap::new();

    for line in output.lines() {
        println!("LINE: {line}");
        let mut parts = line.split(':');

        let label = parts.next().unwrap();
        let values = parts.next().unwrap();

        println!("[{values}]");
        println!("[{}]", values.trim());

        let latencies: Vec<u64> = values
            .trim()
            .split(' ')
            .map(|x| x.parse::<u64>().unwrap())
            .collect();
        println!("{latencies:?}");
        measurements.insert(label.to_string(), Stats::from(latencies.as_slice()));
    }

    Measurements { measurements }
}

fn main() {
    println!("# Running Benchmark: Runtime Measurements");

    let args: Vec<String> = env::args().collect();

    let output = Command::new("git")
        .args(["status", "--porcelain"])
        .output()
        .expect("failed to execute process");

    let is_dirty = !output.stdout.is_empty();
    let build_dirty = env!("VERGEN_GIT_DIRTY") == "true";
    let allow_dirty = args.iter().any(|e| e.as_str() == "--allow-dirty");

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

    let output = match compile_and_run() {
        Ok(output) => output,
        Err(_) => {
            println!("# Benchmark failed");
            return;
        }
    };

    let res = parse_results(&output);

    println!("# Results:");
    println!("{res}");

    println!("# Completed");
    let latex_results = res.to_latex();
    println!("% latex table\n{latex_results}");
}
