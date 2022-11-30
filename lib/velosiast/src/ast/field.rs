// VelosiAst -- a Ast for the Velosiraptor Language
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

//! # VelosiAst -- Generic Field
//!
//! This module defines the State AST nodes of the langauge

use crate::ast::VelosiAstFieldSlice;
use std::rc::Rc;

pub trait VelosiAstField {
    /// obtains a reference to the identifier
    fn ident(&self) -> &Rc<String>;

    /// obtains a copy of the identifer
    fn ident_to_string(&self) -> String;

    /// obtains a reference to the fully qualified path
    fn path(&self) -> &Rc<String>;

    /// obtains a copy of the fully qualified path
    fn path_to_string(&self) -> String;

    /// obtains the layout of the field
    fn layout(&self) -> &[Rc<VelosiAstFieldSlice>];

    /// the size of the field in bits
    fn nbits(&self) -> u64;
}
