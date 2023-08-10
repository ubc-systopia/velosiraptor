// VelosiParser -- a parser for the Velosiraptor Language
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

//! # VelosiParser -- Parse Tree Unit
//!
//! Parse tree nodes for Unit definitions

// used standard library functionality
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

// used parsetree nodes
use crate::parsetree::{
    VelosiParseTreeConstDef, VelosiParseTreeExpr, VelosiParseTreeIdentifier,
    VelosiParseTreeInterface, VelosiParseTreeMap, VelosiParseTreeParam, VelosiParseTreeState,
    VelosiParseTreeType,
};
use crate::VelosiTokenStream;

pub type VelosiParseTreeMethodProperty =
    (VelosiParseTreeIdentifier, Option<VelosiParseTreeIdentifier>);

#[derive(PartialEq, Eq, Clone)]
pub struct VelosiParseTreeMethod {
    /// the name of the unit (identifier)
    pub name: VelosiParseTreeIdentifier,
    /// properties of the method
    pub properties: Vec<VelosiParseTreeMethodProperty>,
    /// whether this is an abstract method
    pub is_abstract: bool,
    /// whether this is a method to be synthesized
    pub is_synth: bool,
    /// the unit parameters
    pub params: Vec<VelosiParseTreeParam>,
    /// the name of the derrived unit
    pub rettype: Option<VelosiParseTreeType>,
    /// the nodes defined in the parse tree
    pub requires: Vec<VelosiParseTreeExpr>,
    /// the body of the method
    pub body: Option<VelosiParseTreeExpr>,
    /// the position in the source tree where this unit is defined
    pub pos: VelosiTokenStream,
}

impl VelosiParseTreeMethod {
    pub fn loc(&self) -> &VelosiTokenStream {
        &self.pos
    }
}

/// Implement the [Display] trait for the [VelosiParseTreeMethod] struct
impl Display for VelosiParseTreeMethod {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if !self.properties.is_empty() {
            write!(f, "  #[")?;
            for (i, prop) in self.properties.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }

                write!(f, "{}", prop.0.name)?;
                if let Some(param) = &prop.1 {
                    write!(f, "({})", param.name)?;
                }
            }
            writeln!(f, "]")?;
        }

        write!(f, "  ")?;
        if self.is_abstract {
            write!(f, "abstract ")?;
        }
        if self.is_synth {
            write!(f, "synth ")?;
        }
        write!(f, "fn {}(", self.name)?;
        for (i, param) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{param}")?;
        }
        if let Some(rtype) = &self.rettype {
            write!(f, ") -> {rtype}")?;
        } else {
            write!(f, ")")?;
        }

        for (i, require) in self.requires.iter().enumerate() {
            if i == 0 {
                writeln!(f)?;
            }
            writeln!(f, "    requires {require}")?;
        }
        if let Some(body) = &self.body {
            writeln!(f, "  {{\n    {body}\n  }}")?;
        }
        Ok(())
    }
}

/// Implementation of [Debug] for [VelosiParseTreeMethod]
impl Debug for VelosiParseTreeMethod {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

/// reprsents a flag
#[derive(PartialEq, Eq, Clone)]
pub struct VelosiParseTreeFlags {
    /// vector of defined flags
    pub flags: Vec<VelosiParseTreeIdentifier>,
    /// the position in the source tree where this unit is defined
    pub pos: VelosiTokenStream,
}

impl VelosiParseTreeFlags {
    /// create a new [VelosiParseTreeFlags] with the given flags and position
    pub fn new(flags: Vec<VelosiParseTreeIdentifier>, pos: VelosiTokenStream) -> Self {
        VelosiParseTreeFlags { flags, pos }
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        &self.pos
    }
}

impl Display for VelosiParseTreeFlags {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "flags = {{ ")?;
        for (i, flag) in self.flags.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", flag.name)?;
        }
        write!(f, " }};")
    }
}

/// Implementation of [Debug] for [VelosiParseTreeFlags]
impl Debug for VelosiParseTreeFlags {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

/// reprsents a flag
#[derive(PartialEq, Eq, Clone)]
pub struct VelosiParseTreeEnum {
    /// vector of defined flags
    pub ident: VelosiParseTreeIdentifier,
    /// the parameters of the enum
    pub params: Vec<VelosiParseTreeIdentifier>,
    /// the position in the source tree where this unit is defined
    pub pos: VelosiTokenStream,
}

impl VelosiParseTreeEnum {
    /// create a new [VelosiParseTreeEnum] with the given flags and position
    pub fn new(
        ident: VelosiParseTreeIdentifier,
        params: Vec<VelosiParseTreeIdentifier>,
        pos: VelosiTokenStream,
    ) -> Self {
        VelosiParseTreeEnum { ident, params, pos }
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        &self.pos
    }
}

impl Display for VelosiParseTreeEnum {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}(", self.ident.name)?;
        for (i, param) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", param.name)?;
        }
        writeln!(f, "),")
    }
}

/// Implementation of [Debug] for [VelosiParseTreeEnum]
impl Debug for VelosiParseTreeEnum {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

/// Represents possible definitions of a unit body
///
/// The enum captures all possible elements of a unit body ([VelosiParseTreeUnitDef]).
///
#[derive(PartialEq, Eq, Clone)]
pub enum VelosiParseTreeUnitNode {
    /// A constant definition
    Const(VelosiParseTreeConstDef),
    /// Input bit width
    InBitWidth(VelosiParseTreeExpr, VelosiTokenStream),
    /// Output bit width
    OutBitWidth(VelosiParseTreeExpr, VelosiTokenStream),
    /// Flag definition
    Flags(VelosiParseTreeFlags),
    /// State definition
    State(VelosiParseTreeState),
    /// Interface definition
    Interface(VelosiParseTreeInterface),
    /// Method definition
    Method(VelosiParseTreeMethod),
    /// Static map definition
    Map(VelosiParseTreeMap),
    /// Enum entry
    EnumEntry(VelosiParseTreeEnum),
}

/// Implement [Display] for [VelosiParseTreeUnitNode]
impl Display for VelosiParseTreeUnitNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            VelosiParseTreeUnitNode::Const(const_def) => {
                write!(f, "  ")?;
                Display::fmt(const_def, f)?;
            }
            VelosiParseTreeUnitNode::InBitWidth(e, _) => {
                write!(f, "  inbitwidth = {e};")?;
            }
            VelosiParseTreeUnitNode::OutBitWidth(e, _) => {
                write!(f, "  outbitwidth = {e};")?;
            }
            VelosiParseTreeUnitNode::Flags(flags) => {
                write!(f, "  ")?;
                Display::fmt(flags, f)?;
            }
            VelosiParseTreeUnitNode::State(state) => {
                write!(f, "  state = ")?;
                Display::fmt(state, f)?;
            }
            VelosiParseTreeUnitNode::Interface(interface) => {
                write!(f, "  interface = ")?;
                Display::fmt(interface, f)?;
            }
            VelosiParseTreeUnitNode::Method(method) => Display::fmt(method, f)?,
            VelosiParseTreeUnitNode::Map(map) => {
                write!(f, "  staticmap = ")?;
                Display::fmt(map, f)?;
            }
            VelosiParseTreeUnitNode::EnumEntry(enum_entry) => {
                write!(f, "  ")?;
                Display::fmt(enum_entry, f)?;
            }
        }
        writeln!(f)
    }
}

/// Implementation of [Debug] for [VelosiParseTreeUnitNode]
impl Debug for VelosiParseTreeUnitNode {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

/// Represents a unit definition
///
/// The unit definition corresponds to the definition of a basic building block
/// in the Velosiraptor language.
///
/// A unit has an identifier that gives it a name. It can be derived from another
/// unit using, similar to inheritance in object oriented programming.
///
/// Units can be parameterized, for example defining the base address. In some
/// way this is a bit like a mixture between templating and constructor values.
///
/// A unit has a set of nodes ([VelosiParseTreeUnitNode]) that contain the definitions
/// of the body of the unit.
///
#[derive(PartialEq, Eq, Clone)]
pub struct VelosiParseTreeUnitDef {
    /// the name of the unit (identifier)
    pub name: VelosiParseTreeIdentifier,
    /// the unit parameters
    pub params: Vec<VelosiParseTreeParam>,
    /// the name of the derrived unit
    pub derived: Option<VelosiParseTreeIdentifier>,
    /// the nodes defined in the parse tree
    pub nodes: Vec<VelosiParseTreeUnitNode>,
    /// whether this is an abstract unit
    pub is_abstract: bool,
    /// the position in the source tree where this unit is defined
    pub loc: VelosiTokenStream,
}

impl VelosiParseTreeUnitDef {
    pub fn new(
        name: VelosiParseTreeIdentifier,
        params: Vec<VelosiParseTreeParam>,
        is_abstract: bool,
        derived: Option<VelosiParseTreeIdentifier>,
        nodes: Vec<VelosiParseTreeUnitNode>,
        loc: VelosiTokenStream,
    ) -> Self {
        VelosiParseTreeUnitDef {
            name,
            params,
            derived,
            nodes,
            is_abstract,
            loc,
        }
    }
}

/// Implement [Display] for [VelosiParseTreeUnitDef]
impl Display for VelosiParseTreeUnitDef {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.name)?;
        if !self.params.is_empty() {
            write!(f, "(")?;
            for (i, param) in self.params.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{param}")?;
            }
            write!(f, ")")?;
        }

        if let Some(derived) = &self.derived {
            write!(f, " : {derived}")?;
        }

        writeln!(f, " {{")?;
        for n in self.nodes.iter() {
            writeln!(f, "{n}")?;
        }

        writeln!(f, "}}")
    }
}

/// Implementation of [Debug] for [VelosiParseTreeUnitDef]
impl Debug for VelosiParseTreeUnitDef {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

/// Unit Node Representation
///
/// A unit in the Velosiraptor language represents a basic building block.
/// There are two kinds of units:
///
///   - the configurable segment
///   - the static map
///
/// While the unit kind dictates the nature of the unit, the parser doesn't
/// restrict the parsing as such. Thus each unit body is defined by the
/// [VelosiParseTreeUnitDef] struct.
///
#[derive(PartialEq, Eq, Clone)]
pub enum VelosiParseTreeUnit {
    /// This unit is a configurable segment
    Segment(VelosiParseTreeUnitDef),
    /// This unit is a static map
    StaticMap(VelosiParseTreeUnitDef),
    /// This is an enum unit
    Enum(VelosiParseTreeUnitDef),
}

impl VelosiParseTreeUnit {
    pub fn loc(&self) -> &VelosiTokenStream {
        match self {
            VelosiParseTreeUnit::Segment(unit) => &unit.loc,
            VelosiParseTreeUnit::StaticMap(unit) => &unit.loc,
            VelosiParseTreeUnit::Enum(unit) => &unit.loc,
        }
    }
}

/// Implement [Display] for [VelosiParseTreeUnit]
impl Display for VelosiParseTreeUnit {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            VelosiParseTreeUnit::Segment(unit) => {
                if unit.is_abstract {
                    write!(f, "abstract ")?;
                }
                write!(f, "segment ")?;
                Display::fmt(&unit, f)
            }
            VelosiParseTreeUnit::StaticMap(unit) => {
                if unit.is_abstract {
                    write!(f, "abstract ")?;
                }
                write!(f, "staticmap ")?;
                Display::fmt(&unit, f)
            }
            VelosiParseTreeUnit::Enum(unit) => {
                write!(f, "enum ")?;
                Display::fmt(&unit, f)
            }
        }
    }
}

/// Implementation of [Debug] for [VelosiParseTreeUnit]
impl Debug for VelosiParseTreeUnit {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
