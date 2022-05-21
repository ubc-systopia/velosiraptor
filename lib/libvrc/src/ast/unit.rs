// Velosiraptor Lexer
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

//! Unit Ast Node
//!
//! This defines a unit node in the AST. The unit node represents a unit definition,
//! and as such a type.

// the used standard library functionality
use std::cmp::Ordering;
use std::fmt::{Debug, Display, Formatter, Result};

// the used crate-internal functionality
use crate::ast::{
    utils, AstNode, AstNodeGeneric, Const, Interface, Issues, Map, Method, Param, State, Symbol,
    SymbolKind, SymbolTable, Type,
};
use crate::error::{ErrorLocation, VrsError};
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
            (Unit::StaticMap(staticmap), Unit::StaticMap(other)) => Unit::StaticMap(staticmap.derives_from(other)),
            (Unit::Segment(segment), Unit::Segment(other)) => Unit::Segment(segment.derives_from(other)),
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

/// Represents a translation unit of the configurable segment type.
///
/// This type of translation unit remaps a contiguous region of memory
/// with a given size by adding a configurable offset to it.
#[derive(PartialEq, Clone)]
pub struct Segment {
    /// the name of the unit (identifier)
    pub name: String,
    /// the unit parameters
    pub params: Vec<Param>,
    /// the name of the derrived unit
    pub derived: Option<String>,
    /// the input bitwidth of the unit
    pub inbitwidth: u64,
    /// the output bitwidth of the unit
    pub outbitwidth: u64,
    /// defined constants in this unit
    pub consts: Vec<Const>,
    /// the state of the unit
    pub state: State,
    /// the software visible interface of the unit
    pub interface: Interface,
    /// the methods defined by this unit
    pub methods: Vec<Method>,
    // TODO: maybe make the translate / constructors / map / ... explicit here?
    /// synthesized map operations for this unit
    pub map_ops: Option<Vec<Operation>>,
    /// synthesizeed unmap operations for this unit
    pub unmap_ops: Option<Vec<Operation>>,
    /// synthesized protect operations for this unit
    pub protect_ops: Option<Vec<Operation>>,
    /// the position in the source tree where this unit is defined
    pub pos: TokenStream,
}

/// Implementation of [Segment]
impl<'a> Segment {
    /// creates a new Segment node
    pub fn new(name: String, params: Vec<Param>, pos: TokenStream) -> Self {
        Segment {
            name,
            params,
            derived: None,
            inbitwidth: 0,
            outbitwidth: 0,
            consts: Vec::new(),
            state: State::new_none(),
            interface: Interface::new_none(),
            methods: Vec::new(),
            map_ops: None,
            unmap_ops: None,
            protect_ops: None,
            pos,
        }
    }

    /// sets the input addressing bit width
    pub fn set_inbitwidth(mut self, inbitwidth: Option<u64>) -> Self {
        self.inbitwidth = inbitwidth.unwrap_or(CFG_DEFAULT_BITWIDTH);
        self
    }

    /// sets the output addressing bit width
    pub fn set_outbitwidth(mut self, outbitwidth: Option<u64>) -> Self {
        self.outbitwidth = outbitwidth.unwrap_or(CFG_DEFAULT_BITWIDTH);
        self
    }

    pub fn set_derived(mut self, derived: Option<String>) -> Self {
        self.derived = derived;
        self
    }

    pub fn set_state(mut self, state: State) -> Self {
        self.state = state;
        self
    }

    pub fn set_interface(mut self, interface: Interface) -> Self {
        self.interface = interface;
        self
    }

    pub fn add_consts(mut self, consts: Vec<Const>) -> Self {
        self.consts.extend(consts);
        self
    }

    pub fn add_methods(mut self, methods: Vec<Method>) -> Self {
        self.methods.extend(methods);
        self
    }

    /// finalized the unit
    pub fn finalize(mut self, pos: &TokenStream) -> Self {
        self.pos = self.pos.expand_until(pos);
        self
    }

    pub fn location(&self) -> String {
        self.pos.location()
    }

    pub fn to_symbol(&self) -> Symbol {
        Symbol::new(
            self.name.clone(),
            Type::Unit,
            SymbolKind::Unit,
            self.loc().clone(),
            AstNode::Segment(self),
        )
    }

    /// Obtains the method with the given name
    pub fn get_method(&self, name: &str) -> Option<&Method> {
        self.methods.iter().find(|m| m.name == name)
    }

    /// Obtains the derived element of the segment if any
    pub fn derived(&self) -> Option<&String> {
        self.derived.as_ref()
    }

    pub fn methods(&self) -> &[Method] {
        &self.methods
    }

    pub fn consts(&self) -> &[Const] {
        &self.consts
    }

    pub fn interface(&self) -> &Interface {
        &self.interface
    }

    pub fn state(&self) -> &State {
        &self.state
    }

    pub fn map_ops(&self) -> Option<&Vec<Operation>> {
        self.map_ops.as_ref()
    }

    pub fn vaddr_max(&self) -> u64 {
        if self.inbitwidth < 64 {
            (1u64 << self.inbitwidth) - 1
        } else {
            u64::MAX
        }
    }

    pub fn paddr_max(&self) -> u64 {
        if self.outbitwidth < 64 {
            (1u64 << self.outbitwidth) - 1
        } else {
            u64::MAX
        }
    }

    /// derives [Self] from the other unit
    ///
    /// This pulls in the definitions, constants, etc from the other unit.
    /// Unit elements that are defined in [Self] will not be overwritten by the other unit.
    pub fn derive(&mut self, other: &Segment) {
        assert!(self.derived.is_some());
        assert_eq!(self.derived.as_ref().unwrap(), other.name.as_str());
        println!("unit: {} deriving form {}", self.name, other.name());

        // merge params
        for p in other.params.iter() {
            if !self.params.iter().any(|x| x.name == p.name) {
                self.params.push(p.clone());
            }
        }

        // merge methods
        for m in other.methods.iter() {
            if !self.methods.iter().any(|x| x.name == m.name) {
                self.methods.push(m.clone());
            }
        }
        // merge interface

        // merge state
    }

    /// derives a new unit from self and another unit
    pub fn derives_from(&self, other: &Segment) -> Self {
        let mut u = self.clone();
        u.derive(other);
        u
    }
}

/// implementation of the [fmt::Display] trait for the [Segment]
impl Display for Segment {
    fn fmt(&self, f: &mut Formatter) -> Result {
        writeln!(f, "Segment {}", self.name)?;
        if let Some(d) = &self.derived {
            writeln!(f, " : {}", d)?;
        }
        writeln!(f, "{{\nTODO\n}}")
    }
}

/// implementation of the [fmt::Debug] trait for the [Segment]
impl Debug for Segment {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let line = self.loc().line();
        let column = self.loc().column();

        writeln!(f, "{:03}:{:03} | Segment {}", line, column, self.name)?;
        if let Some(d) = &self.derived {
            writeln!(f, " : {}", d)?;
        }
        writeln!(f, "{{\nTODO\n}}")
    }
}

/// Implemetation of the [AstNodeGeneric] trait for [Unit]
impl<'a> AstNodeGeneric<'a> for Segment {
    fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
        // all fine for now
        let mut res = Issues::ok();

        let name = self.name();
        let pos = self.loc();

        // set the current context
        st.create_context(String::from(self.name()));

        // adding the module paramters
        for p in &self.params {
            if !st.insert(p.to_symbol()) {
                res.inc_err(1);
            }
        }

        // adding the constants
        for c in &self.consts {
            if !st.insert(c.to_symbol()) {
                res.inc_err(1);
            }
        }

        // add the methods to it
        for m in &self.methods {
            if !st.insert(m.to_symbol()) {
                res.inc_err(1);
            }
        }

        // add the state symbolds
        // XXX: maybe we wan to do the symbol table building after checking the elements?
        self.state.build_symboltable(st);
        self.interface.build_symboltable(st);

        // Check 1: Double defined constants
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check that all constants of this field have distinct names
        // Notes:       --
        // --------------------------------------------------------------------------------------

        let errors = utils::check_double_entries(&self.consts);
        res.inc_err(errors);

        // Check 2: Constants
        // --------------------------------------------------------------------------------------
        // Type:        Error/Warning
        // Description: Check all defined constats of the Unit
        // Notes:
        // --------------------------------------------------------------------------------------
        for c in &self.consts {
            res = res + c.check(st);
        }

        // Check 3: State Check
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Error
        // Description: Check that the state definition is fine
        // Notes:       --
        // --------------------------------------------------------------------------------------

        if self.state.is_none() {
            let msg = format!("missing state definition for unit `segment {}`", self.name);
            let hint = String::from("add the state definition `state = Register | Memory` here");
            VrsError::new_err(self.pos.with_range(0..2), msg, Some(hint)).print();
            res.inc_err(1);
        }

        // check the state and interface
        res = res + self.state.check(st);

        // Check 4: State Param Check
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Error
        // Description: Check that the state refers to actual parameters
        // Notes:       --
        // --------------------------------------------------------------------------------------
        // TODO: check params

        // Check 5: Interface Check
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Error
        // Description: Check that the state definition is fine
        // Notes:       --
        // --------------------------------------------------------------------------------------

        if self.interface.is_none() {
            let msg = format!(
                "missing interface definition for unit `segment {}`",
                self.name
            );
            let hint =
                String::from("add the interface definition `interface = Register | Memory` here");
            VrsError::new_err(self.pos.with_range(0..2), msg, Some(hint)).print();
            res.inc_err(1);
        }

        res = res + self.interface.check(st);

        // Check 6: Interface param check
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Error
        // Description: Check that the interface refers to actual parameters
        // Notes:       --
        // --------------------------------------------------------------------------------------
        // TODO: check params / field refs

        // Check 7: Methods double defined
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Error
        // Description: Check double method definition
        // Notes:       --
        // --------------------------------------------------------------------------------------

        let errors = utils::check_double_entries(&self.methods);
        res.inc_err(errors);

        // Check 8: Method check
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Error
        // Description: Check that the interface refers to actual parameters
        // Notes:       --
        // --------------------------------------------------------------------------------------

        for m in &self.methods {
            res = res + m.check(st);
        }

        // Check 9: Bases are defined
        // --------------------------------------------------------------------------------------
        // Type:        Warning
        // Description: Check if the unit name is CamelCase
        // Notes:       --
        // --------------------------------------------------------------------------------------
        res = res + utils::check_camel_case(name, pos);

        // Check 10: Translate/Map methods defined
        // --------------------------------------------------------------------------------------
        // Type:        Error/Warning
        // Description: Check all defined constats of the Unit
        // Notes:
        // --------------------------------------------------------------------------------------

        let mut has_map = false;
        let mut has_translate = false;
        let mut has_matchflags = false;
        for m in &self.methods {
            match m.name() {
                "translate" => {
                    has_translate = true;
                }
                "map" => {
                    has_map = true;
                }
                "matchflags" => {
                    has_matchflags = true;
                }
                "remap" => {}
                _ => {}
            }
        }

        if !has_translate {
            let msg = format!("translate() method not defined for unit `{}`", name);
            let hint = format!("implement the translate() method for unit `{}`", name);
            VrsError::new_err(pos.with_range(0..2), msg, Some(hint)).print();
            res.inc_err(1);
        }

        if !has_matchflags {
            let msg = format!("matchflags() method not defined for unit `{}`", name);
            let hint = format!("implement the matchflags() method for unit `{}`", name);
            VrsError::new_err(pos.with_range(0..2), msg, Some(hint)).print();
            res.inc_err(1);
        }

        if !has_map {
            let msg = format!("map() method not defined for unit `{}`", name);
            let hint = format!("implement the map() method for unit `{}`", name);
            VrsError::new_err(pos.with_range(0..2), msg, Some(hint)).print();
            res.inc_err(1);
        }

        st.drop_context();
        res
    }

    /// returns the location of the current
    fn loc(&self) -> &TokenStream {
        &self.pos
    }

    fn name(&self) -> &str {
        self.name.as_str()
    }
}

/// Rep
#[derive(PartialEq, Clone)]
pub struct StaticMap {
    /// the name of the unit (identifier)
    pub name: String,
    /// the unit parameters
    pub params: Vec<Param>,
    /// the name of the derived unit
    pub derived: Option<String>,
    /// the input bit width of the unit
    pub inbitwidth: u64,
    /// the outbit width with of the unit
    pub outbitwidth: u64,
    /// defined constants in this unit
    pub consts: Vec<Const>,
    /// Optional map in the case of map UnitType
    pub map: Option<Map>,
    /// the methods defined by this unit
    pub methods: Vec<Method>,
    /// the position in the source tree where this unit is defined
    pub pos: TokenStream,
}

/// Implementation of [Unit]
impl<'a> StaticMap {
    /// creates a new Segment node
    pub fn new(name: String, params: Vec<Param>, pos: TokenStream) -> Self {
        StaticMap {
            name,
            params,
            derived: None,
            inbitwidth: 0,
            outbitwidth: 0,
            consts: Vec::new(),
            methods: Vec::new(),
            map: None,
            pos,
        }
    }

    /// sets the input addressing bit width
    pub fn set_inbitwidth(mut self, inbitwidth: Option<u64>) -> Self {
        self.inbitwidth = inbitwidth.unwrap_or(CFG_DEFAULT_BITWIDTH);
        self
    }

    /// sets the output addressing bit width
    pub fn set_outbitwidth(mut self, outbitwidth: Option<u64>) -> Self {
        self.outbitwidth = outbitwidth.unwrap_or(CFG_DEFAULT_BITWIDTH);
        self
    }

    pub fn set_derived(mut self, derived: Option<String>) -> Self {
        self.derived = derived;
        self
    }

    pub fn set_map(mut self, map: Map) -> Self {
        self.map = Some(map);
        self
    }

    pub fn add_consts(mut self, consts: Vec<Const>) -> Self {
        self.consts.extend(consts);
        self
    }

    pub fn add_methods(mut self, methods: Vec<Method>) -> Self {
        self.methods.extend(methods);
        self
    }

    /// finalized the unit
    pub fn finalize(mut self, pos: &TokenStream) -> Self {
        self.pos = self.pos.expand_until(pos);
        self
    }

    pub fn location(&self) -> String {
        self.pos.location()
    }

    pub fn to_symbol(&self) -> Symbol {
        Symbol::new(
            self.name.clone(),
            Type::Unit,
            SymbolKind::Unit,
            self.loc().clone(),
            AstNode::StaticMap(self),
        )
    }

    /// Obtains the derived element of the segment if any
    pub fn derived(&self) -> Option<&String> {
        self.derived.as_ref()
    }

    pub fn methods(&self) -> &[Method] {
        &self.methods
    }

    pub fn consts(&self) -> &[Const] {
        &self.consts
    }

    pub fn interface(&self) -> &Interface {
        &crate::ast::NONE_INTERFACE
    }

    pub fn state(&self) -> &State {
        &crate::ast::NONE_STATE
    }

    pub fn map_ops(&self) -> Option<&Vec<Operation>> {
        None
    }

    pub fn vaddr_max(&self) -> u64 {
        todo!("need to figure out teh maps first");
    }
    pub fn paddr_max(&self) -> u64 {
        todo!("need to figure out teh maps first");
    }

    /// derives [Self] from the other unit
    ///
    /// This pulls in the definitions, constants, etc from the other unit.
    /// Unit elements that are defined in [Self] will not be overwritten by the other unit.
    pub fn derive(&mut self, other: &StaticMap) {
        assert!(self.derived.is_some());
        assert_eq!(self.derived.as_ref().unwrap(), other.name.as_str());
        println!("unit: {} deriving form {}", self.name, other.name());

        // merge params
        for p in other.params.iter() {
            if !self.params.iter().any(|x| x.name == p.name) {
                self.params.push(p.clone());
            }
        }

        // merge methods
        for m in other.methods.iter() {
            if !self.methods.iter().any(|x| x.name == m.name) {
                self.methods.push(m.clone());
            }
        }
        // merge interface

        // merge state
    }

    /// derives a new unit from self and another unit
    pub fn derives_from(&self, other: &StaticMap) -> Self {
        let mut u = self.clone();
        u.derive(other);
        u
    }
}

/// implementation of the [fmt::Display] trait for the [StaticMap]
impl Display for StaticMap {
    fn fmt(&self, f: &mut Formatter) -> Result {
        writeln!(f, "StaticMap {}", self.name)?;
        if let Some(d) = &self.derived {
            writeln!(f, " : {}", d)?;
        }
        writeln!(f, "{{\nTODO\n}}")
    }
}

/// implementation of the [fmt::Debug] trait for the [StaticMap]
impl Debug for StaticMap {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let line = self.loc().line();
        let column = self.loc().column();

        writeln!(f, "{:03}:{:03} | StaticMap {}", line, column, self.name)?;
        if let Some(d) = &self.derived {
            writeln!(f, " : {}", d)?;
        }
        writeln!(f, "{{\nTODO\n}}")
    }
}

/// Implemetation of the [AstNodeGeneric] trait for [StaticMap]
impl<'a> AstNodeGeneric<'a> for StaticMap {
    /// performs the ast checks for the StaticMap
    fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
        // all fine for now
        let mut res = Issues::ok();

        let name = self.name();
        let pos = self.loc();

        // set the current context
        st.create_context(String::from(self.name()));

        // adding the module paramters
        for p in &self.params {
            if !st.insert(p.to_symbol()) {
                res.inc_err(1);
            }
        }

        // adding the constants
        for c in &self.consts {
            if !st.insert(c.to_symbol()) {
                res.inc_err(1);
            }
        }

        // add the methods to it
        for m in &self.methods {
            if !st.insert(m.to_symbol()) {
                res.inc_err(1);
            }
        }

        // Check 1: Double defined constants
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check that all constants of this field have distinct names
        // Notes:       --
        // --------------------------------------------------------------------------------------

        let errors = utils::check_double_entries(&self.consts);
        res.inc_err(errors);

        // Check 2: Constants
        // --------------------------------------------------------------------------------------
        // Type:        Error/Warning
        // Description: Check all defined constats of the Unit
        // Notes:
        // --------------------------------------------------------------------------------------
        for c in &self.consts {
            res = res + c.check(st);
        }

        // Check 4: State Param Check
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Error
        // Description: Check that the state refers to actual parameters
        // Notes:       --
        // --------------------------------------------------------------------------------------
        // TODO: check params

        // Check 7: Methods double defined
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Error
        // Description: Check double method definition
        // Notes:       --
        // --------------------------------------------------------------------------------------

        let errors = utils::check_double_entries(&self.methods);
        res.inc_err(errors);

        // Check 8: Method check
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Error
        // Description: Check that the interface refers to actual parameters
        // Notes:       --
        // --------------------------------------------------------------------------------------

        for m in &self.methods {
            res = res + m.check(st);
        }

        // Check 9: Bases are defined
        // --------------------------------------------------------------------------------------
        // Type:        Warning
        // Description: Check if the unit name is CamelCase
        // Notes:       --
        // --------------------------------------------------------------------------------------
        res = res + utils::check_camel_case(name, pos);

        st.drop_context();
        res
    }

    /// returns the location of the StaticMap
    fn loc(&self) -> &TokenStream {
        &self.pos
    }

    /// returns the name of the StaticName
    fn name(&self) -> &str {
        self.name.as_str()
    }
}
