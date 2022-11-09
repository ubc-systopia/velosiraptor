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

//! # VelosiAst -- Generif Field
//!
//! This module defines the State AST nodes of the langauge


/// represents the generic part of a field
struct VelosiAstField {
    /// the name of the unit
    pub ident: VelosiAstIdentifier,
    /// the size of the field
    pub size: u64,
    /// layout of the field
    pub layout: Vec<Rc<VelosiAstFieldSlice>>,
    /// hashmap of the layout from slice name to slice
    pub layout_map: HashMap<String, Rc<VelosiAstFieldSlice>>,
}

/// represents a memory reference
struct VelsiAstMemoryRef {
    /// base this field is part of
    pub base: VelosiAstIdentifier,
    /// offset of this field within the base
    pub offset: u64,
}

/// represents a memory field
struct VelosiAstMemField {
    field: VelosiAstField,
    memref: VelsiAstMemoryRef,
}

/// represents a register field
struct VelosiAstRegField(pub VelosiAstField);


