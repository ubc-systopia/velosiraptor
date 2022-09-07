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

use std::path::PathBuf;
use std::sync::Arc;
use std::thread;
use std::thread::JoinHandle;

use smt2::Smt2File;

use crate::synth::Operation;

struct Z3Task {
    base: Arc<Smt2File>,
    available_ops: Vec<Operation>,
    thread: Option<JoinHandle<Vec<Operation>>>,
    success: bool,
}

impl Z3Task {
    pub fn new(smt: Arc<Smt2File>, ops: Vec<Operation>) -> Self {
        Z3Task {
            base: smt,
            available_ops: ops,
            thread: None,
            success: false,
        }
    }

    pub fn exec(&mut self) {
        // add the goal
        //self.base.add_comment("foooobar");

        let path = PathBuf::from("foo.smt2");
        let mut smt = Smt2File::empty();

        self.base.extend_and_save_as(&smt, &path);

        self.thread = Some(thread::spawn(move || {
            println!("executing: {}", path.display());
            println!("ok!");
            Vec::new()
        }));
    }

    pub fn started(&self) -> bool {
        self.thread.is_some()
    }

    pub fn finished(&self) -> bool {
        if let Some(thread) = &self.thread {
            thread.is_finished()
        } else {
            false
        }
    }

    pub fn result(&mut self) -> Result<Vec<Operation>, ()> {
        if self.thread.is_none() {
            return Err(());
        }

        let thread = self.thread.take().unwrap();
        Ok(thread.join().unwrap())
    }
}
