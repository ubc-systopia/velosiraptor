// VelosiHwGen -- A hardware generator for the Velosiraptor language
//
//
// MIT License
//
// Copyright (c) 2021, 2022 Systopia Lab, Computer Science, University of British Columbia
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

use std::{env, path::Path};
use velosiast::{AstResult, VelosiAst};
use velosihwgen::VelosiHwGen;

pub fn main() {
    let args: Vec<String> = env::args().collect();

    let ast = match args.len() {
        2 => VelosiAst::from_file(&args[1]),
        _ => {
            println!("Usage: velosihwgen <file>");
            return;
        }
    };

    let ast = match ast {
        AstResult::Ok(ast) => ast,
        AstResult::Issues(ast, err) => {
            println!("{}", err);
            ast
        }
        AstResult::Err(err) => {
            println!("{}", err);
            return;
        }
    };

    let vrs_file = Path::new(&args[1]).file_stem();
    let unit_name = match vrs_file {
        Some(p) => p.to_string_lossy().into_owned(),
        None => "unknown_vrs".to_owned(),
    };

    let hwgen = VelosiHwGen::new_fastmodels(Path::new("./out"), unit_name);

    hwgen
        .prepare()
        .expect("could not prepare the hwgen backend");

    if let Err(e) = hwgen.generate(&ast) {
        log::error!(target: "main", "code generation failed\n{:?}", e);
    }

    hwgen.finalize(&ast).expect("could not finalize");
}
