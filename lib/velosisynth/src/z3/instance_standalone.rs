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
use std::io::{BufRead, BufReader, Read, Write};
use std::os::fd::AsRawFd;
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::time::Instant;

// use nonblock::NonBlockingReader;

use super::query::{Z3Query, Z3Result, Z3Ticket, Z3TimeStamp};
use super::Z3Error;

/// flag whether we want to use a full restart when resetting z3
const CONFIG_RESET_IS_RESTART: bool = true;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Z3 Instance
////////////////////////////////////////////////////////////////////////////////////////////////////

// https://stackoverflow.com/questions/34611742/how-do-i-read-the-output-of-a-child-process-without-blocking-in-rust

use libc::{fcntl, F_GETFL, F_SETFL, O_NONBLOCK};

fn set_nonblocking<H>(handle: &H, nonblocking: bool) -> std::io::Result<()>
where
    H: Read + AsRawFd,
{
    let fd = handle.as_raw_fd();
    let flags = unsafe { fcntl(fd, F_GETFL, 0) };
    if flags < 0 {
        return Err(std::io::Error::last_os_error());
    }
    let flags = if nonblocking {
        flags | O_NONBLOCK
    } else {
        flags & !O_NONBLOCK
    };
    let res = unsafe { fcntl(fd, F_SETFL, flags) };
    if res != 0 {
        return Err(std::io::Error::last_os_error());
    }
    Ok(())
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Z3 Instance
////////////////////////////////////////////////////////////////////////////////////////////////////

pub struct Z3Async {
    t_start: Instant,
    t_prepare: Instant,
    pub ticket: Z3Ticket,
    // query: &'a mut Z3Query,
    result: String,
}

/// represents a Z3 instance that that runs queries
pub struct Z3Instance {
    /// the identifier of this instance
    id: usize,
    /// whether we're currently executing a query
    is_executing: bool,
    /// the z3 process instance
    z3_proc: Child,
    /// the path to where the logfiles are stored
    logfile: Option<File>,
    /// some statistics of the instance
    stats: Z3InstanceStats,
}

impl Z3Instance {
    /// creates a new z3 instance with the given identifier
    pub fn new(id: usize) -> Self {
        log::trace!(target : "[Z3Instance]", "{} creating new", id);

        Z3Instance {
            id,
            is_executing: false,
            z3_proc: Self::spawn_z3(),
            logfile: None,
            stats: Z3InstanceStats::new(),
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
            is_executing: false,
            z3_proc: Self::spawn_z3(),
            logfile,
            stats: Z3InstanceStats::new(),
        }
    }

    /// spawns a new z3 process
    fn spawn_z3() -> Child {
        let mut proc = Command::new("z3")
            .arg("-in")
            .arg("-smt2")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .expect("Failed to spawn z3 process, is z3 installed?");

        if let Some(z3_stdout) = proc.stdout.as_mut() {
            // create a buffer reader for the z3_stdout
            set_nonblocking(z3_stdout, true).expect("huh");
        }

        proc
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
        self.stats.reset();
        self.terminate();
        self.is_executing = false;
        self.z3_proc = Self::spawn_z3();
    }

    /// resets the z3 instance, by sending a `(reset)` command
    pub fn reset(&mut self) -> Result<(), Z3Error> {
        self.stats.reset();
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

    pub fn exec_async(
        &mut self,
        ticket: Z3Ticket,
        query: &mut Z3Query,
    ) -> Result<Z3Async, Z3Error> {
        log::debug!(target : "[Z3Instance]", "{} executing query", self.id);

        if self.is_executing {
            return Err(Z3Error::WorkerBusy);
        }

        self.is_executing = true;

        let t_start = Instant::now();

        // write the commands to the z3 process' stdin
        if let Some(z3_stdin) = self.z3_proc.stdin.as_mut() {
            // can we format/write this directly into the stdin?

            let id = format!(";; Z3Ticket({})\n", ticket);

            // record the time to create the smt context
            query.timestamp(Z3TimeStamp::FmtSmt);

            // send it to z3
            z3_stdin.write_all(id.as_bytes()).unwrap();
            if let Some(f) = &mut self.logfile {
                f.write_all(id.as_bytes())
                    .expect("writing the smt query failed.");
            }

            let mut buf_string = String::with_capacity(2 * 4096);
            for smt in query.smt_contexts() {
                if query.get_retries() > 0 {
                    let rand = std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .unwrap()
                        .as_millis();
                    let push = format!("(push)(set-option :timeout {})(set-option :smt.random_seed {})(set-option :sat.random_seed {})(declare-const x{} (_ BitVec 32))\n",
                            250 + query.get_retries() * 50,
                            rand,
                            rand,
                            rand);
                    buf_string.push_str(push.as_str());
                    smt.to_code_into(!cfg!(debug_assertions), &mut buf_string);
                    buf_string.push_str("(pop)\n");

                    log::info!("Retrying Query:");
                    log::info!(
                        "-------------------------------------------------------------------"
                    );
                    log::info!("{buf_string}");
                    log::info!(
                        "-------------------------------------------------------------------"
                    );
                } else {
                    smt.to_code_into(!cfg!(debug_assertions), &mut buf_string);
                };
                z3_stdin.write_all(buf_string.as_bytes()).unwrap();

                if let Some(f) = &mut self.logfile {
                    f.write_all(buf_string.as_bytes())
                        .expect("writing the smt query failed.");
                }
                buf_string.clear();
            }

            // record the time to execute the query
            query.timestamp(Z3TimeStamp::SendCmd);

            // adding an `(echo)` to have at least some output
            z3_stdin
                .write_all("\n(echo \"!remove\")\n".as_bytes())
                .unwrap();

            let t_prepare = Instant::now();
            Ok(Z3Async {
                t_start,
                t_prepare,
                ticket,
                // query,
                result: String::with_capacity(256),
            })
        } else {
            Err(Z3Error::QueryExecution)
        }
    }

    pub fn exec_done(&mut self, asynctok: Z3Async) -> Result<Z3Result, Z3Async> {
        let Z3Async {
            t_start,
            t_prepare,
            ticket,
            // query,
            mut result,
        } = asynctok;

        // read back the results from stdout
        log::trace!(target : "[Z3Instance]", "{} obtaining query results", self.id);

        let result = if let Some(z3_stdout) = self.z3_proc.stdout.as_mut() {
            let mut z3_buf_reader = BufReader::new(z3_stdout);
            loop {
                let mut line = String::with_capacity(256);
                if let Ok(_sz) = z3_buf_reader.read_line(&mut line) {
                    // if it's our magic string, then we're done
                    if line.as_str() == "!remove\n" {
                        break;
                    }
                    result.push_str(&line);
                } else {
                    return Err(Z3Async {
                        t_start,
                        t_prepare,
                        ticket,
                        // query,
                        result,
                    });
                }
            }
            result
        } else {
            String::new()
        };

        let t_query = Instant::now();
        let t_query = t_query.duration_since(t_prepare).as_millis() as u64;
        let t_prepare = t_prepare.duration_since(t_start).as_millis() as u64;

        self.stats.add(ticket.0, t_prepare, t_query);

        self.is_executing = false;

        log::trace!(target : "[Z3Instance]", "{} query result is '{}'", self.id, result);
        Ok(Z3Result::new(result))
    }

    ///executes the query
    pub fn exec(&mut self, ticket: Z3Ticket, query: &mut Z3Query) -> Result<Z3Result, Z3Error> {
        match self.exec_async(ticket, query) {
            Ok(mut tok) => loop {
                tok = match self.exec_done(tok) {
                    Ok(res) => return Ok(res),
                    Err(tok) => tok,
                };
            },
            Err(e) => Err(e),
        }
    }

    ///executes the query
    pub fn exec_shared(&mut self, query: &Z3Query) -> Result<Z3Result, Z3Error> {
        log::trace!(target : "[Z3Instance]", "{} executing shared query", self.id);

        let t_start = Instant::now();

        // write the commands to the z3 process' stdin
        if let Some(z3_stdin) = self.z3_proc.stdin.as_mut() {
            // can we format/write this directly into the stdin?

            // construt the smt2 context from the query
            let contexts = query.smt_contexts();

            // send to the z3 process
            for smt in contexts {
                z3_stdin
                    .write_all(smt.to_code(!cfg!(debug_assertions)).as_bytes())
                    .unwrap();
            }
            // adding an `(echo)` to have at least some output
            z3_stdin
                .write_all("\n(echo \"!remove\")\n".as_bytes())
                .unwrap();

            if let Some(f) = &mut self.logfile {
                for smt in contexts {
                    f.write_all(smt.to_code(!cfg!(debug_assertions)).as_bytes())
                        .expect("writing the smt query failed.");
                }
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
                if let Ok(_sz) = z3_buf_reader.read_line(&mut line) {
                    // if it's our magic string, then we're done
                    if line.as_str() == "!remove\n" {
                        break;
                    }
                    result.push_str(&line);
                }
            }
            result
        } else {
            String::new()
        };

        let t_query = Instant::now();
        let t_query = t_query.duration_since(t_prepare).as_millis() as u64;
        let t_prepare = t_prepare.duration_since(t_start).as_millis() as u64;
        self.stats.add(0, t_prepare, t_query);

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

////////////////////////////////////////////////////////////////////////////////////////////////////
// Z3 Instance Stats
////////////////////////////////////////////////////////////////////////////////////////////////////

pub struct Z3InstanceStats {
    /// cumulative time for preparing queries
    pub t_prepare: u64,
    /// cummulative time for executing queries
    pub t_query: u64,
    /// longest running query time
    pub t_longest_query: u64,
    /// id of the longest running query
    pub id_longest_query: usize,
    /// number of queries executed
    pub num_queries: u64,
}

impl Z3InstanceStats {
    pub fn new() -> Self {
        Self {
            t_prepare: 0,
            t_query: 0,
            t_longest_query: 0,
            id_longest_query: 0,
            num_queries: 0,
        }
    }

    pub fn reset(&mut self) {
        self.t_prepare = 0;
        self.t_query = 0;
        self.t_longest_query = 0;
        self.id_longest_query = 0;
        self.num_queries = 0;
    }

    pub fn add(&mut self, id: usize, t_prepare: u64, t_query: u64) {
        self.t_prepare += t_prepare;
        self.t_query += t_query;
        if t_query > self.t_longest_query {
            self.t_longest_query = t_query;
            self.id_longest_query = id;
        }
        self.num_queries += 1;
    }
}
