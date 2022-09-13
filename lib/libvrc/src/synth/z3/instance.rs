// Velosiraptor Synthesizer
//
//
// MIT License
//
// Copyright (c) 2021 Systopia Lab, Computer Science, University of British Columbia
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

use std::fs::{self, File};
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};

use super::query::{Z3Query, Z3Result};

/// flag whether we want to use a full restart when resetting z3
const CONFIG_RESET_IS_RESTART: bool = false;

/// represents a Z3 instance that that runs queries
pub struct Z3Instance {
    /// the identifier of this instance
    id: usize,
    /// the z3 process instance
    z3_proc: Child,
    /// the path to where the logfiles are stored
    logfile: Option<File>,
}

impl Z3Instance {
    /// creates a new z3 instance with the given identifier
    pub fn new(id: usize) -> Self {
        println!("[z3-inst-{}] creating new", id);

        Z3Instance {
            id,
            z3_proc: Self::spawn_z3(),
            logfile: None,
        }
    }

    /// creates a new Z3 instace with the supplied log path
    pub fn with_logpath(id: usize, logpath: &PathBuf) -> Self {
        println!(
            "[z3-inst-{}] creating new with log {}",
            id,
            logpath.display()
        );

        // create the log directory if it does not exist
        fs::create_dir_all(logpath).expect("failed to create the log directory");

        // construct the log file in the path, and create the file
        let p = logpath.join(format!("z3-worker-{}-log.smt2", id));
        let logfile = match File::create(p) {
            Ok(f) => Some(f),
            Err(e) => {
                println!("[z3-inst-{}] failed to create the file: {}", id, e);
                None
            }
        };

        Z3Instance {
            id,
            z3_proc: Self::spawn_z3(),
            logfile,
        }
    }

    /// spawns a new z3 process
    fn spawn_z3() -> Child {
        Command::new("z3")
            .arg("-in")
            .arg("-smt2")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .expect("Failed to spawn z3 process, is z3 installed?")
    }

    /// terminates the z3 instance
    pub fn terminate(&mut self) {
        self.z3_proc.kill();
        self.z3_proc
            .wait()
            .expect("waiting for process termination failed");
    }

    /// restarts the z3 instance, terminate it and restart it
    pub fn restart(&mut self) {
        self.terminate();
        self.z3_proc = Self::spawn_z3();
    }

    /// resets the z3 instance, by sending a `(reset)` command
    pub fn reset(&mut self) -> Result<(), ()> {
        if CONFIG_RESET_IS_RESTART {
            self.restart();
            Ok(())
        } else {
            match self.exec(&Z3Query::reset()) {
                Ok(r) => Ok(()),
                Err(e) => {
                    println!("[z3-inst-{}] failed to reset", self.id);
                    Err(())
                }
            }
        }
    }

    ///executes the query
    pub fn exec(&mut self, query: &Z3Query) -> Result<Z3Result, ()> {
        println!("[z3-inst-{}] writing commands", self.id);

        // write the commands to the z3 process' stdin
        if let Some(z3_stdin) = self.z3_proc.stdin.as_mut() {
            // can we format/write this directly into the stdin?

            // construt the smt2 context from the query
            let smt = query.smt_context().to_string();

            // send to the z3 process
            z3_stdin.write_all(smt.as_bytes()).unwrap();
            // adding an `(echo)` to have at least some output
            z3_stdin
                .write_all("\n(echo \"!remove\")\n".as_bytes())
                .unwrap();

            if let Some(f) = &mut self.logfile {
                f.write_all(smt.as_bytes());
            }
        } else {
            return Err(());
        }

        // read back the results from stdout
        println!("[z3-inst-{}] reading results...", self.id);

        let result = if let Some(z3_stdout) = self.z3_proc.stdout.as_mut() {
            // create a buffer reader for the z3_stdout
            let mut z3_buf_reader = BufReader::new(z3_stdout);
            // store the result here
            let mut result = String::with_capacity(1024);

            // loop over the result
            loop {
                let mut line = String::with_capacity(256);
                z3_buf_reader.read_line(&mut line).unwrap();

                // if it's our magic string, then we're done
                if line.as_str() == "!remove\n" {
                    break;
                }
                result.push_str(&line);
            }
            result
        } else {
            String::new()
        };

        println!("[z3-inst-{}] result '{}'", self.id, result);
        Ok(Z3Result::new(result))
    }
}

impl Drop for Z3Instance {
    fn drop(&mut self) {
        self.terminate();
    }
}
