// Velosiraptor Ast
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

//! Unit Ast Node
//!
//! This defines a unit node in the AST. The unit node represents a unit definition,
//! and as such a type.

// the used standard library functionality
use std::cmp::Ordering;
use std::fmt::{Debug, Display, Formatter, Result};

// module components
mod segment;
mod staticmap;

pub use segment::Segment;
pub use staticmap::StaticMap;

use crate::ast::{AstNodeGeneric, Const, Interface, Issues, Method, State, Symbol, SymbolTable};
use crate::synth::Operation;
use crate::token::TokenStream;

pub const CFG_DEFAULT_BITWIDTH: u64 = 64;

/// Defines a translation unit
///
/// A translation unit is either a [StaticMap] or a [Segment] and describes the personality
/// of a component that remapps memory requests.
///
/// Moreover, a translation unit may be derived from another unit, similar
/// to inheritance in other languages.
#[derive(PartialEq, Clone)]
pub enum Unit {
    StaticMap(StaticMap),
    Segment(Segment),
}

/// Implementation of [Unit]
impl<'a> Unit {
    pub fn location(&self) -> String {
        match self {
            Unit::StaticMap(staticmap) => staticmap.location(),
            Unit::Segment(segment) => segment.location(),
        }
    }

    pub fn to_symbol(&self) -> Symbol {
        match self {
            Unit::StaticMap(staticmap) => staticmap.to_symbol(),
            Unit::Segment(segment) => segment.to_symbol(),
        }
    }

    /// obtains a method with a given anme
    pub fn get_method(&self, name: &str) -> Option<&Method> {
        match self {
            Unit::StaticMap(_) => None,
            Unit::Segment(segment) => segment.get_method(name),
        }
    }

    pub fn derived(&self) -> Option<&String> {
        match self {
            Unit::StaticMap(staticmap) => staticmap.derived(),
            Unit::Segment(segment) => segment.derived(),
        }
    }
    pub fn methods(&self) -> &[Method] {
        match self {
            Unit::StaticMap(staticmap) => staticmap.methods(),
            Unit::Segment(segment) => segment.methods(),
        }
    }

    pub fn consts(&self) -> &[Const] {
        match self {
            Unit::StaticMap(staticmap) => staticmap.consts(),
            Unit::Segment(segment) => segment.consts(),
        }
    }

    pub fn interface(&self) -> &Interface {
        match self {
            Unit::StaticMap(staticmap) => staticmap.interface(),
            Unit::Segment(segment) => segment.interface(),
        }
    }

    pub fn state(&self) -> &State {
        match self {
            Unit::StaticMap(staticmap) => staticmap.state(),
            Unit::Segment(segment) => segment.state(),
        }
    }

    pub fn map_ops(&self) -> Option<&Vec<Operation>> {
        match self {
            Unit::StaticMap(staticmap) => staticmap.map_ops(),
            Unit::Segment(segment) => segment.map_ops(),
        }
    }

    pub fn vaddr_max(&self) -> u64 {
        match self {
            Unit::StaticMap(staticmap) => staticmap.vaddr_max(),
            Unit::Segment(segment) => segment.vaddr_max(),
        }
    }

    pub fn paddr_max(&self) -> u64 {
        match self {
            Unit::StaticMap(staticmap) => staticmap.paddr_max(),
            Unit::Segment(segment) => segment.paddr_max(),
        }
    }

    pub fn derive(&mut self, other: &Unit) {
        match (self, other) {
            (Unit::StaticMap(staticmap), Unit::StaticMap(other)) => staticmap.derive(other),
            (Unit::Segment(segment), Unit::Segment(other)) => segment.derive(other),
            _ => {
                panic!("Derivation type mismatch!")
            }
        }
    }

    pub fn derives_from(self, other: &Unit) -> Self {
        match (self, other) {
            (Unit::StaticMap(staticmap), Unit::StaticMap(other)) => {
                Unit::StaticMap(staticmap.derives_from(other))
            }
            (Unit::Segment(segment), Unit::Segment(other)) => {
                Unit::Segment(segment.derives_from(other))
            }
            _ => {
                panic!("Derivation type mismatch!")
            }
        }
    }
}

/// implementation of the [fmt::Display] trait for the [Unit]
impl Display for Unit {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            Unit::StaticMap(staticmap) => Display::fmt(&staticmap, f),
            Unit::Segment(segment) => Display::fmt(&segment, f),
        }
    }
}

/// implementation of the [fmt::Debug] trait for the [Unit]
impl Debug for Unit {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            Unit::StaticMap(staticmap) => Debug::fmt(&staticmap, f),
            Unit::Segment(segment) => Debug::fmt(&segment, f),
        }
    }
}

/// implementation of [PartialOrd] for [Import]
impl PartialOrd for Unit {
    /// This method returns an ordering between self and other values if one exists.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // we jus compare with the TokenStream position
        self.loc().partial_cmp(other.loc())
    }
}

/// Implemetation of the [AstNodeGeneric] trait for [Unit]
impl<'a> AstNodeGeneric<'a> for Unit {
    fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
        match self {
            Unit::StaticMap(staticmap) => staticmap.check(st),
            Unit::Segment(segment) => segment.check(st),
        }
    }

    /// returns the location of the current
    fn loc(&self) -> &TokenStream {
        match self {
            Unit::StaticMap(staticmap) => staticmap.loc(),
            Unit::Segment(segment) => segment.loc(),
        }
    }

    fn name(&self) -> &str {
        match self {
            Unit::StaticMap(staticmap) => staticmap.name(),
            Unit::Segment(segment) => segment.name(),
        }
    }
}
