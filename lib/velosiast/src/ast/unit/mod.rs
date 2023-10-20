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

//! # VelosiAst -- Unit Definitions
//!
//! This module defines the Constant AST nodes of the language

// modules
mod enums;
mod osspec;
mod segment;
mod staticmap;

// re-exports
pub use enums::VelosiAstUnitEnum;
pub use osspec::VelosiAstUnitOSSpec;
pub use segment::VelosiAstUnitSegment;
pub use staticmap::VelosiAstUnitStaticMap;

// used standard library functionality

use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::parsetree::{VelosiParseTreeProperty, VelosiParseTreeUnit};
use velosiparser::VelosiTokenStream;

// used crate functionality
use crate::error::{VelosiAstErrBuilder, VelosiAstIssues};
use crate::{AstResult, Symbol, SymbolTable};

// used definitions of references AST nodes
use crate::ast::{
    types::{VelosiAstType, VelosiAstTypeInfo},
    VelosiAstConst, VelosiAstFlags, VelosiAstInterface, VelosiAstMethod, VelosiAstMethodProperty,
    VelosiAstNode, VelosiAstParam, VelosiAstState,
};

// used definitions of references AST nodes
#[macro_export]
macro_rules! unit_ignore_node (
    ($node:path, $pst:expr, $issues:expr, $kind:expr) => {
       {
            let msg = format!("Ignored unit node: {} definitions are not supported in {}.",
            stringify!($node), $kind);
            let hint = "Remove this definition.";
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint.to_string())
                .add_location($pst.loc().clone())
                .build();
            $issues.push(err);
        }
    }
);

////////////////////////////////////////////////////////////////////////////////////////////////////
// Units
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Defines an Unit AST node
#[derive(PartialEq, Eq, Clone)]
pub enum VelosiAstUnit {
    Segment(Rc<VelosiAstUnitSegment>),
    StaticMap(Rc<VelosiAstUnitStaticMap>),
    Enum(Rc<VelosiAstUnitEnum>),
    OSSpec(Rc<VelosiAstUnitOSSpec>),
}

impl VelosiAstUnit {
    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        pt: VelosiParseTreeUnit,
        st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        use VelosiParseTreeUnit::*;
        match pt {
            Segment(pt) => VelosiAstUnitSegment::from_parse_tree(pt, st),
            StaticMap(pt) => VelosiAstUnitStaticMap::from_parse_tree(pt, st),
            Enum(pt) => VelosiAstUnitEnum::from_parse_tree(pt, st),
            OSSpec(pt) => VelosiAstUnitOSSpec::from_parse_tree(pt, st),
        }
    }

    /// obtains a reference to the identifier
    pub fn ident(&self) -> &Rc<String> {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.ident(),
            StaticMap(s) => s.ident(),
            Enum(e) => e.ident(),
            OSSpec(e) => e.ident(),
        }
    }

    /// obtains a copy of the identifer
    pub fn ident_to_string(&self) -> String {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.ident_to_string(),
            StaticMap(s) => s.ident_to_string(),
            Enum(e) => e.ident_to_string(),
            OSSpec(e) => e.ident_to_string(),
        }
    }

    /// obtains a reference to the fully qualified path
    pub fn path(&self) -> &Rc<String> {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.path(),
            StaticMap(s) => s.path(),
            Enum(e) => e.path(),
            OSSpec(e) => e.path(),
        }
    }

    /// obtains a copy of the fully qualified path
    pub fn path_to_string(&self) -> String {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.path_to_string(),
            StaticMap(s) => s.path_to_string(),
            Enum(e) => e.path_to_string(),
            OSSpec(e) => e.path_to_string(),
        }
    }

    /// whether the unit is abstract or conceret
    pub fn is_abstract(&self) -> bool {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.is_abstract,
            StaticMap(_) => false,
            Enum(_) => false,
            OSSpec(_) => false,
        }
    }

    pub fn is_segment(&self) -> bool {
        matches!(self, VelosiAstUnit::Segment(_))
    }

    pub fn is_staticmap(&self) -> bool {
        matches!(self, VelosiAstUnit::StaticMap(_))
    }

    pub fn is_enum(&self) -> bool {
        matches!(self, VelosiAstUnit::Enum(_))
    }

    pub fn is_osspec(&self) -> bool {
        matches!(self, VelosiAstUnit::OSSpec(_))
    }

    pub fn params_as_slice(&self) -> &[Rc<VelosiAstParam>] {
        use VelosiAstUnit::*;
        match self {
            Segment(pt) => pt.params_as_slice(),
            StaticMap(pt) => pt.params_as_slice(),
            Enum(pt) => pt.params_as_slice(),
            OSSpec(pt) => pt.params_as_slice(),
        }
    }

    pub fn input_bitwidth(&self) -> u64 {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.inbitwidth,
            StaticMap(s) => s.inbitwidth,
            Enum(e) => e.inbitwidth,
            OSSpec(_e) => panic!("output bit width not defined of OSSpec"),
        }
    }

    pub fn output_bitwidth(&self) -> u64 {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.outbitwidth,
            StaticMap(s) => s.outbitwidth,
            Enum(e) => e.outbitwidth,
            OSSpec(_e) => panic!("output bit width not defined of OSSpec"),
        }
    }

    pub fn vaddr_max(&self) -> u64 {
        use VelosiAstUnit::*;
        match self {
            StaticMap(staticmap) => staticmap.vaddr_max(),
            Segment(segment) => segment.vaddr_max(),
            Enum(e) => e.vaddr_max(),
            OSSpec(e) => e.vaddr_max(),
        }
    }

    pub fn paddr_max(&self) -> u64 {
        use VelosiAstUnit::*;
        match self {
            StaticMap(staticmap) => staticmap.paddr_max(),
            Segment(segment) => segment.paddr_max(),
            Enum(e) => e.paddr_max(),
            OSSpec(_e) => unreachable!(),
        }
    }

    pub fn methods(&self) -> Box<dyn Iterator<Item = &Rc<VelosiAstMethod>> + '_> {
        use VelosiAstUnit::*;
        match self {
            StaticMap(staticmap) => Box::new(staticmap.methods()),
            Segment(segment) => Box::new(segment.methods()),
            Enum(_) => Box::new(std::iter::empty()),
            OSSpec(e) => Box::new(e.methods()),
        }
    }

    pub fn methods_with_property(&self, prop: VelosiAstMethodProperty) -> Vec<Rc<VelosiAstMethod>> {
        self.methods()
            .filter(|m| m.properties.contains(&prop))
            .cloned()
            .collect()
    }

    pub fn get_method(&self, name: &str) -> Option<&Rc<VelosiAstMethod>> {
        use VelosiAstUnit::*;
        match self {
            StaticMap(staticmap) => staticmap.get_method(name),
            Segment(segment) => segment.get_method(name),
            Enum(_) => None,
            OSSpec(o) => o.get_method(name),
        }
    }

    pub fn get_method_with_signature(
        &self,
        params: &[VelosiAstTypeInfo],
        rtype: &VelosiAstTypeInfo,
    ) -> Vec<Rc<VelosiAstMethod>> {
        use VelosiAstUnit::*;
        match self {
            StaticMap(staticmap) => staticmap.get_method_with_signature(params, rtype),
            Segment(segment) => segment.get_method_with_signature(params, rtype),
            Enum(e) => e.get_method_with_signature(params, rtype),
            OSSpec(o) => o.get_method_with_signature(params, rtype),
        }
    }

    pub fn consts(&self) -> Box<dyn Iterator<Item = &Rc<VelosiAstConst>> + '_> {
        use VelosiAstUnit::*;
        match self {
            StaticMap(staticmap) => Box::new(staticmap.consts()),
            Segment(segment) => Box::new(segment.consts()),
            Enum(_) => Box::new(std::iter::empty()),
            OSSpec(o) => Box::new(o.consts()),
        }
    }

    pub fn flags(&self) -> Option<Rc<VelosiAstFlags>> {
        use VelosiAstUnit::*;
        match self {
            StaticMap(_) => None,
            Segment(segment) => segment.flags.clone(),
            Enum(_) => None,
            OSSpec(_) => None,
        }
    }

    pub fn interface(&self) -> Option<Rc<VelosiAstInterface>> {
        use VelosiAstUnit::*;
        match self {
            StaticMap(_) => None,
            Segment(segment) => Some(segment.interface.clone()),
            Enum(_) => None,
            OSSpec(_) => None,
        }
    }

    pub fn compare_interface(&self, other: &VelosiAstUnit) -> bool {
        use VelosiAstUnit::*;
        match (self, other) {
            (Segment(s1), Segment(s2)) => s1.interface.compare(&s2.interface),
            (StaticMap(_), StaticMap(_)) => true,
            (Enum(_), Enum(_)) => true,
            (OSSpec(_), OSSpec(_)) => true,
            _ => false,
        }
    }

    pub fn state(&self) -> Option<Rc<VelosiAstState>> {
        use VelosiAstUnit::*;
        match self {
            StaticMap(_) => None,
            Segment(segment) => Some(segment.state.clone()),
            Enum(_) => None,
            OSSpec(_) => None,
        }
    }

    pub fn compare_state(&self, other: &VelosiAstUnit) -> bool {
        use VelosiAstUnit::*;
        match (self, other) {
            (Segment(s1), Segment(s2)) => s1.state.compare(&s2.state),
            (StaticMap(_), StaticMap(_)) => true,
            (Enum(_), Enum(_)) => true,
            (OSSpec(_), OSSpec(_)) => true,
            _ => false,
        }
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => &s.loc,
            StaticMap(s) => &s.loc,
            Enum(e) => &e.loc,
            OSSpec(e) => &e.loc,
        }
    }

    pub fn get_next_unit_idents(&self) -> Vec<&Rc<String>> {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.get_next_unit_idents(),
            StaticMap(s) => s.get_next_unit_idents(),
            Enum(e) => e.get_next_unit_idents(),
            OSSpec(_e) => Vec::new(),
        }
    }

    pub fn has_memory_state(&self) -> bool {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.has_memory_state(),
            StaticMap(s) => s.has_memory_state(),
            Enum(s) => s.has_memory_state(),
            OSSpec(_e) => false,
        }
    }
}

/// Implementation fo the [From] trait for [Symbol]
impl From<VelosiAstUnit> for Symbol {
    fn from(unit: VelosiAstUnit) -> Self {
        let ti = VelosiAstType::from(unit.clone());
        let name = unit.path().clone();
        Symbol::new(name, ti, VelosiAstNode::Unit(unit))
    }
}

/// Implementation fo the [From] trait for [Symbol]
impl From<VelosiAstUnit> for VelosiAstType {
    fn from(unit: VelosiAstUnit) -> Self {
        let name = unit.ident().clone();
        VelosiAstType::new(VelosiAstTypeInfo::TypeRef(name), unit.loc().clone())
    }
}

/// Implementation of [Display] for [VelosiAstUnit]
impl Display for VelosiAstUnit {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            VelosiAstUnit::Segment(s) => Display::fmt(s, f),
            VelosiAstUnit::StaticMap(s) => Display::fmt(s, f),
            VelosiAstUnit::Enum(e) => Display::fmt(e, f),
            VelosiAstUnit::OSSpec(o) => Display::fmt(o, f),
        }
    }
}

/// Implementation of [Debug] for [VelosiAstUnit]
impl Debug for VelosiAstUnit {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub enum VelosiAstUnitProperty {
    ArrayRepr,
    ListRepr,
    None,
}

impl VelosiAstUnitProperty {
    pub fn from_parse_tree(
        pt: VelosiParseTreeProperty,
        _st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        match pt.ident.name.as_str() {
            "repr" => match pt.params.as_slice() {
                [arg] => match arg.name.as_str() {
                    "array" => AstResult::Ok(Self::ArrayRepr),
                    "list" => AstResult::Ok(Self::ListRepr),
                    _ => {
                        let msg = "invalid argument";
                        let hint = "repr property expects either `array` or `list`";
                        let err = VelosiAstErrBuilder::err(msg.to_string())
                            .add_hint(hint.to_string())
                            .add_location(pt.loc)
                            .build();
                        AstResult::Err(VelosiAstIssues::from(err))
                    }
                },
                _ => {
                    let msg = "repr requires one argument. ";
                    let hint = "repr property expects either `array` or `list`";
                    let err = VelosiAstErrBuilder::err(msg.to_string())
                        .add_hint(hint.to_string())
                        .add_location(pt.loc)
                        .build();
                    AstResult::Err(VelosiAstIssues::from(err))
                }
            },
            p => {
                let msg = format!("unsupported unit property {p}");
                let hint = "supported method properties are `repr(list|array)`";
                let err = VelosiAstErrBuilder::err(msg)
                    .add_hint(hint.to_string())
                    .add_location(pt.loc)
                    .build();
                AstResult::Issues(Self::None, VelosiAstIssues::from(err))
            }
        }
    }
}

impl Display for VelosiAstUnitProperty {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::ArrayRepr => write!(f, "repr(array)"),
            Self::ListRepr => write!(f, "repr(list)"),
            Self::None => Ok(()),
        }
    }
}

/// Implementation of [Debug] for [VelosiAstUnitProperty]
impl Debug for VelosiAstUnitProperty {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
