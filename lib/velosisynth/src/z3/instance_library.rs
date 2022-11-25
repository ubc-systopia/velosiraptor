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

use std::ffi::CStr;
use std::ffi::CString;
use std::fs::{File};
use std::io::{Write};

use std::path::PathBuf;
use std::time::Instant;

// the z3 dependency
use z3_sys::*;

use super::query::{Z3Query, Z3Result, Z3Ticket};
use super::Z3Error;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Z3 Instance
////////////////////////////////////////////////////////////////////////////////////////////////////

/// represents a Z3 instance that that runs queries
pub struct Z3Instance {
    /// the identifier of this instance
    id: usize,
    /// the z3 context
    z3_context: Option<Z3_context>,
    z3_config: Option<Z3_config>,

    /// the path to where the logfiles are stored
    logfile: Option<File>,

    t_prepare: u64,
    t_query: u64,
}

extern "C" fn error_handler(ctx: Z3_context, _code: ErrorCode) {
    // println!("error handler: error code: {:?}", code);
    // println!("message: ");

    unsafe {
        // let mut z3res = Z3_get_error_msg(ctx, code);
        // while *z3res != 0 {
        //     print!("{}", *z3res as u8 as char);
        //     z3res = z3res.add(1);
        // }
        Z3_set_error(ctx, ErrorCode::OK);
    }

    // println!("message end.");
}

impl Z3Instance {
    /// creates a new z3 instance with the given identifier
    pub fn new(id: usize) -> Self {
        log::trace!(target : "[Z3Instance]", "{} creating new", id);

        let (z3_context, z3_config) = Self::create_z3_context();

        Z3Instance {
            id,
            z3_context: Some(z3_context),
            z3_config: Some(z3_config),
            logfile: None,
            t_prepare: 0,
            t_query: 0,
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

        let (z3_context, z3_config) = Self::create_z3_context();

        Z3Instance {
            id,
            z3_context: Some(z3_context),
            z3_config: Some(z3_config),
            logfile,
            t_prepare: 0,
            t_query: 0,
        }
    }

    // create a new z3 context
    fn create_z3_context() -> (Z3_context, Z3_config) {
        let cfg = unsafe {
            let cfg = Z3_mk_config();
            let param = CString::new("encoding").expect("foobar");
            let value = CString::new("ascii").expect("foobar");
            Z3_set_param_value(cfg, param.as_ptr(), value.as_ptr());
            cfg
        };
        let ctx = unsafe { Z3_mk_context(cfg) };
        unsafe {
            Z3_set_error_handler(ctx, Some(error_handler));
        }
        (ctx, cfg)
    }

    /// terminates the z3 instance
    pub fn terminate(&mut self) {
        if let Some(ctx) = self.z3_context.take() {
            unsafe { Z3_del_context(ctx) };
        }
        if let Some(cfg) = self.z3_config.take() {
            unsafe { Z3_del_config(cfg) };
        }
    }

    /// restarts the z3 instance, terminate it and restart it
    pub fn restart(&mut self) {
        self.terminate();
        let (ctx, cfg) = Self::create_z3_context();
        self.z3_context = Some(ctx);
        self.z3_config = Some(cfg);
    }

    /// resets the z3 instance, by sending a `(reset)` command
    pub fn reset(&mut self) -> Result<(), Z3Error> {
        if cfg!(feature = "z3-restart") {
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
    pub fn exec(&mut self, _ticket: Z3Ticket, query: &mut Z3Query) -> Result<Z3Result, Z3Error> {
        log::info!(target : "[Z3Instance]", "{} executing query", self.id);

        let t_start = Instant::now();

        // construt the smt2 context from the query
        let smt = query.smt_context().to_code(!cfg!(debug_assertions));

        // query.timestamp("writesmt");
        if let Some(f) = &mut self.logfile {
            f.write_all(smt.as_bytes())
                .expect("writing the smt query failed.");
        }

        let mut smt_bytes = smt.into_bytes();
        // add the null terminator
        smt_bytes.push(0);

        let c_string = CString::from_vec_with_nul(smt_bytes).expect("foobar");

        let mut result = String::with_capacity(256);

        let t_prepare = Instant::now();

        unsafe {
            let z3res = Z3_eval_smtlib2_string(self.z3_context.unwrap(), c_string.as_ptr());

            let c_str: &CStr = unsafe { CStr::from_ptr(z3res) };
            let str_slice: &str = c_str.to_str().unwrap();
            result.push_str(str_slice);

            // release the returned memory pointer
            // Z3_finalize_memory();
        };

        let t_query = Instant::now();

        self.t_prepare += t_prepare.duration_since(t_start).as_millis() as u64;
        self.t_query += t_query.duration_since(t_prepare).as_millis() as u64;

        log::info!(target : "[Z3Instance]", "{} query result is '{}'", self.id, result);
        Ok(Z3Result::new(result))
    }

    ///executes the query
    pub fn exec_shared(&mut self, query: &Z3Query) -> Result<Z3Result, Z3Error> {
        log::info!(target : "[Z3Instance]", "{} executing shared query", self.id);

        let t_start = Instant::now();

        // construt the smt2 context from the query
        let smt = query.smt_context().to_code(!cfg!(debug_assertions));

        // query.timestamp("writesmt");
        if let Some(f) = &mut self.logfile {
            f.write_all(smt.as_bytes())
                .expect("writing the smt query failed.");
        }

        let mut smt_bytes = smt.into_bytes();
        // add the null terminator
        smt_bytes.push(0);

        let c_string = CString::from_vec_with_nul(smt_bytes).expect("foobar");

        let mut result = String::with_capacity(256);

        let t_prepare = Instant::now();

        unsafe {
            let z3res = Z3_eval_smtlib2_string(self.z3_context.unwrap(), c_string.as_ptr());

            let c_str: &CStr = unsafe { CStr::from_ptr(z3res) };
            let str_slice: &str = c_str.to_str().unwrap();
            result.push_str(str_slice);

            // release the returned memory pointer
            // Z3_finalize_memory();
        };

        let t_query = Instant::now();

        self.t_prepare += t_prepare.duration_since(t_start).as_millis() as u64;
        self.t_query += t_query.duration_since(t_prepare).as_millis() as u64;

        log::info!(target : "[Z3Instance]", "{} query result is '{}'", self.id, result);

        Ok(Z3Result::new(result))
    }
}

impl Drop for Z3Instance {
    fn drop(&mut self) {
        println!(
            "[Z3LibraryInstance]   prepare time: {}ms, query time: {}ms",
            self.t_prepare, self.t_query
        );

        self.terminate();
    }
}
