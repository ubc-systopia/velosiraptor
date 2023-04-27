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

use std::fs::File;
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::time::Instant;

use super::query::{Z3Query, Z3Result, Z3Ticket};
use super::Z3Error;

/// flag whether we want to use a full restart when resetting z3
const CONFIG_RESET_IS_RESTART: bool = false;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Z3 Instance
////////////////////////////////////////////////////////////////////////////////////////////////////

/// represents a Z3 instance that that runs queries
pub struct Z3Instance {
    /// the identifier of this instance
    id: usize,
    /// the z3 process instance
    z3_proc: Child,
    /// the path to where the logfiles are stored
    logfile: Option<File>,

    t_prepare: u64,
    t_query: u64,
    t_longest_query: u64,
    num_queries: u64,
}

impl Z3Instance {
    /// creates a new z3 instance with the given identifier
    pub fn new(id: usize) -> Self {
        log::trace!(target : "[Z3Instance]", "{} creating new", id);

        Z3Instance {
            id,
            z3_proc: Self::spawn_z3(),
            logfile: None,
            t_prepare: 0,
            t_query: 0,
            t_longest_query: 0,
            num_queries: 0,
        }
    }

    /// creates a new Z3 instace with the supplied log path
    pub fn with_logfile(id: usize, logfile: PathBuf) -> Self {
        log::trace!(
            target : "[Z3Instance]", "{} creating new with logfile {}",
            id,
            logfile.display()
        );

        // construct the log file in the path, and create the file
        let logfile = match File::create(logfile) {
            Ok(f) => Some(f),
            Err(e) => {
                log::warn!(target : "[Z3Instance]", "{} failed to create the file ({})", id, e);
                None
            }
        };

        Z3Instance {
            id,
            z3_proc: Self::spawn_z3(),
            logfile,
            t_prepare: 0,
            t_query: 0,
            t_longest_query: 0,
            num_queries: 0,
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
        if self.z3_proc.kill().is_ok() {
            log::info!(target : "[Z3Instance]", "{} forcefully terminated z3 instance", self.id);
        }
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
    pub fn reset(&mut self) -> Result<(), Z3Error> {
        if CONFIG_RESET_IS_RESTART {
            self.restart();
            Ok(())
        } else {
            match self.exec(Z3Ticket(0), &mut Z3Query::reset()) {
                Ok(_) => Ok(()),
                Err(e) => {
                    log::error!(target : "[Z3Instance]", "{} failed to reset", self.id);
                    Err(e)
                }
            }
        }
    }

    ///executes the query
    pub fn exec(&mut self, ticket: Z3Ticket, query: &mut Z3Query) -> Result<Z3Result, Z3Error> {
        log::debug!(target : "[Z3Instance]", "{} executing query", self.id);

        let t_start = Instant::now();

        // write the commands to the z3 process' stdin
        if let Some(z3_stdin) = self.z3_proc.stdin.as_mut() {
            // can we format/write this directly into the stdin?

            // construt the smt2 context from the query
            let smt = query.smt_context().to_code(!cfg!(debug_assertions));
            // query.timestamp("fmtsmt");

            let id = format!(";; Z3Ticket({})\n", ticket);

            // send to the z3 process
            z3_stdin.write_all(id.as_bytes()).unwrap();

            // send to the z3 process
            z3_stdin.write_all(smt.as_bytes()).unwrap();

            // adding an `(echo)` to have at least some output
            z3_stdin
                .write_all("\n(echo \"!remove\")\n".as_bytes())
                .unwrap();

            // query.timestamp("writesmt");
            if let Some(f) = &mut self.logfile {
                f.write_all(id.as_bytes())
                    .expect("writing the smt query failed.");
                f.write_all(smt.as_bytes())
                    .expect("writing the smt query failed.");
            }
            // query.timestamp("logging");
        } else {
            return Err(Z3Error::QueryExecution);
        }

        let t_prepare = Instant::now();

        // read back the results from stdout
        log::trace!(target : "[Z3Instance]", "{} obtaining query results", self.id);

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

        let t_query = Instant::now();
        let t_query = t_query.duration_since(t_prepare).as_millis() as u64;
        self.t_prepare += t_prepare.duration_since(t_start).as_millis() as u64;
        self.t_query += t_query;

        self.t_longest_query = std::cmp::max(self.t_longest_query, t_query);
        self.num_queries += 1;

        log::trace!(target : "[Z3Instance]", "{} query result is '{}'", self.id, result);
        Ok(Z3Result::new(result))
    }

    ///executes the query
    pub fn exec_shared(&mut self, query: &Z3Query) -> Result<Z3Result, Z3Error> {
        log::trace!(target : "[Z3Instance]", "{} executing shared query", self.id);

        let t_start = Instant::now();

        // write the commands to the z3 process' stdin
        if let Some(z3_stdin) = self.z3_proc.stdin.as_mut() {
            // can we format/write this directly into the stdin?

            // construt the smt2 context from the query
            let smt = query.smt_context().to_code(!cfg!(debug_assertions));

            // send to the z3 process
            z3_stdin.write_all(smt.as_bytes()).unwrap();
            // adding an `(echo)` to have at least some output
            z3_stdin
                .write_all("\n(echo \"!remove\")\n".as_bytes())
                .unwrap();

            if let Some(f) = &mut self.logfile {
                f.write_all(smt.as_bytes())
                    .expect("writing the smt query failed.");
            }
        } else {
            return Err(Z3Error::QueryExecution);
        }

        let t_prepare = Instant::now();

        // read back the results from stdout
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

        let t_query = Instant::now();
        let t_query = t_query.duration_since(t_prepare).as_millis() as u64;
        self.t_prepare += t_prepare.duration_since(t_start).as_millis() as u64;
        self.t_query += t_query;

        self.t_longest_query = std::cmp::max(self.t_longest_query, t_query);
        self.num_queries += 1;

        Ok(Z3Result::new(result))
    }
}

impl Drop for Z3Instance {
    fn drop(&mut self) {
        // println!(
        //     "[Z3StandaloneInstance] #{} prepare time: {}ms, query time: {}ms, longest query: {}ms, num queries: {}",            self.id, self.t_prepare, self.t_query, self.t_longest_query, self.num_queries
        // );
        self.terminate();
    }
}
