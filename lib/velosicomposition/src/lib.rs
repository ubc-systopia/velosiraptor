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

//! # VelosiCompositino -- Composing Higher-Level Units
//!
//!
//!
//!

// used standard library functionality

use std::ops::Sub;
use std::rc::Rc;

//use std::fmt::{Display, Formatter, Result as FmtResult};

use std::collections::{HashMap, HashSet};
use velosiast::ast::{VelosiAstStaticMap, VelosiAstUnit};
use velosiast::{VelosiAst, VelosiAstUnitStaticMap};

// public re-exports

// struct Composition {
//     pub name: Rc<String>,
//     pub segments: Vec<HLComposition>,
// }

// struct Frame {
//     pub minsize: u64,
//     pub maxsize: u64,
//     pub alignment: u64,
// }

// pub enum HLComposition {
//     Composition(pub Composition),
//     Frame(pub Frame),
// }

pub struct Relations {
    /// relations between the units. unit id -> unit id
    relations: HashMap<Rc<String>, Vec<Rc<String>>>,
    /// the root units
    roots: HashSet<Rc<String>>,
    /// all units
    all_units: HashMap<Rc<String>, VelosiAstUnit>,
    /// units that form a "root" of a group of
    group_roots: HashSet<Rc<String>>,
}

impl Relations {
    pub fn new() -> Self {
        Relations {
            relations: HashMap::new(),
            all_units: HashMap::new(),
            roots: HashSet::new(),
            group_roots: HashSet::new(),
        }
    }

    pub fn from_ast(ast: &VelosiAst) -> Self {
        let units = ast.units();
        let mut relations = Self::new();

        for unit in units {
            if unit.is_abstract() {
                continue;
            }
            match unit {
                VelosiAstUnit::Segment(u) => {
                    let mmap = u.get_method("map").unwrap();
                    let next = mmap.get_param("pa").unwrap();
                    if next.ptype.is_typeref() {
                        let next_unit = next.ptype.typeref().unwrap();
                        relations.do_insert(
                            unit.clone(),
                            vec![ast.get_unit(next_unit).unwrap().clone()],
                        );
                    } else if next.ptype.is_addr() {
                        // nothing to be done
                        relations.do_insert(unit.clone(), Vec::new());
                    } else {
                        unreachable!()
                    }
                }
                VelosiAstUnit::StaticMap(u) => {
                    let next_units = u
                        .get_next_unit_idents()
                        .iter()
                        .map(|u| ast.get_unit(u).unwrap().clone())
                        .collect();
                    relations.do_insert(unit.clone(), next_units);
                }
                VelosiAstUnit::Enum(u) => {
                    let next_units = u
                        .get_next_unit_idents()
                        .iter()
                        .map(|u| ast.get_unit(u).unwrap().clone())
                        .collect();
                    relations.do_insert(unit.clone(), next_units);
                }
                VelosiAstUnit::OSSpec(_) => (),
            }
        }

        relations.update_roots();
        relations.update_group_roots();
        relations
    }

    /// obtains the root unit identifiers
    pub fn get_roots(&self) -> &HashSet<Rc<String>> {
        &self.roots
    }

    /// obtains the root units from the ast
    pub fn get_root_units(&self) -> Vec<VelosiAstUnit> {
        self.roots
            .iter()
            .map(|u| self.all_units.get(u).unwrap().clone())
            .collect()
    }

    /// obtains the identifiers for the group units
    pub fn get_group_roots(&self) -> &HashSet<Rc<String>> {
        &self.group_roots
    }

    /// obtains the units of the group roots
    pub fn get_group_root_units(&self) -> Vec<VelosiAstUnit> {
        self.group_roots
            .iter()
            .map(|u| self.all_units.get(u).unwrap().clone())
            .collect()
    }

    fn do_insert(&mut self, parent: VelosiAstUnit, children: Vec<VelosiAstUnit>) {
        let key = parent.ident().clone();
        self.all_units.insert(key.clone(), parent.clone());
        for child in children.iter() {
            self.all_units.insert(child.ident().clone(), child.clone());
        }
        let entry = self.relations.entry(key).or_insert_with(Vec::new);
        entry.extend(children.iter().map(|u| u.ident().clone()));
    }

    /// obtains the next root units from the given starting unit
    fn update_group_roots(&self) {
        // here we select the
        let mut res = HashSet::new();

        let mut units: Vec<Rc<String>> = self.roots.iter().map(|u| u.clone()).collect();

        // add the root units here, this covers enums and segments here
        for unit in &units {
            res.insert(unit.clone());
        }

        while let Some(unit_ident) = units.pop() {
            let mut unit = self.all_units.get(&unit_ident).unwrap();
            loop {
                // the next units
                let empty = Vec::new();
                let next_idents = self.relations.get(unit.ident()).unwrap_or(&empty);
                let next_units: Vec<_> = next_idents
                    .iter()
                    .map(|unit| self.all_units.get(unit).unwrap())
                    .collect();
                match unit {
                    VelosiAstUnit::Segment(u) => {
                        // segments indicate a break in the unit hierarchy where they map to
                        // another unit, there is just one type here
                        assert!(next_units
                            .iter()
                            .all(|u| u.is_segment() || u.is_enum() || u.is_staticmap()));
                        assert!(next_units.len() <= 1);
                        if let Some(next) = next_idents.first() {
                            res.insert(next.clone());
                            // recurse
                            units.push(next.clone());
                        } else {
                            // we reached the last one
                        }
                        break;
                    }
                    VelosiAstUnit::StaticMap(u) => {
                        // a static map is the "root" of the group, so we need to figure out
                        // the next units that are reachable from that one, there may be multiple
                        // segments here
                        assert!(next_units.iter().all(|u| u.is_segment() || u.is_enum()));
                        if next_units.len() > 1 {
                            unimplemented!("handle me!");
                        }
                        // we just have one type here, add it and return
                        unit = next_units.first().unwrap().clone();
                    }
                    VelosiAstUnit::Enum(u) => {
                        // enum must map to a segment, there may be multiple segments here
                        assert!(next_units.iter().all(|u| u.is_segment()));
                        for u in next_units {
                            assert!(u.is_segment());
                            let variant_idents = self.relations.get(u.ident()).unwrap_or(&empty);
                            let variant_units: Vec<_> = variant_idents
                                .iter()
                                .map(|unit| self.all_units.get(unit).unwrap())
                                .collect();

                            assert!(variant_units
                                .iter()
                                .all(|u| u.is_segment() || u.is_enum() || u.is_staticmap()));
                            assert!(variant_units.len() <= 1);
                            if let Some(next) = variant_units.first() {
                                res.insert(next.ident().clone());
                                units.push(next.ident().clone());
                            } else {
                                // we reached the last one
                            }
                        }
                        break;
                    }
                    VelosiAstUnit::OSSpec(_) => unreachable!(),
                }
            }
        }

        for v in res {
            println!("Unit: {v}");
        }
    }

    fn update_roots(&mut self) {
        let all_units: HashSet<Rc<String>> = self.relations.keys().map(|f| f.clone()).collect();
        let mut referenced_units = HashSet::new();

        for units in self.relations.values() {
            for unit in units.iter() {
                referenced_units.insert(unit.clone());
            }
        }

        let roots = all_units.sub(&referenced_units);

        // println!("all_units {all_units:?}");
        // println!("referenced_units {referenced_units:?}");
        // println!("roots: {roots:?}");

        self.roots = roots
            .iter()
            .map(|f| {
                println!("{}", f);
                self.all_units.get(f).unwrap().ident().clone()
            })
            .collect();
    }

    pub fn insert(&mut self, parent: VelosiAstUnit, children: Vec<VelosiAstUnit>) {
        self.do_insert(parent, children);
        self.update_roots();
        self.update_group_roots();
    }

    pub fn get_children(&self, ident: &Rc<String>) -> &[Rc<String>] {
        if let Some(rels) = self.relations.get(ident) {
            rels.as_slice()
        } else {
            &[]
        }
    }

    pub fn get_children_units(&self, ident: &Rc<String>) -> Vec<VelosiAstUnit> {
        if let Some(rels) = self.relations.get(ident) {
            rels.iter()
                .map(|u| self.all_units.get(u).unwrap().clone())
                .collect()
        } else {
            Vec::new()
        }
    }

    fn do_print_unit_hierarchy(&self, rootid: &Rc<String>, indent: usize) {
        let root = self.all_units.get(rootid).unwrap();

        use VelosiAstUnit::*;
        let prefix = match root {
            Segment(_u) => "~ ",
            StaticMap(_u) => {
                println!();
                "# "
            }
            Enum(_u) => "",
            OSSpec(_) => "",
        };

        println!(
            "{}{}{} ({})",
            " ".repeat(indent),
            prefix,
            root.ident(),
            root.input_bitwidth()
        );

        match root {
            Segment(u) => {
                let mmap = u.get_method("map").unwrap();
                for r in &mmap.requires {
                    println!("{} - {}", " ".repeat(indent + 2), r);
                }
            }
            StaticMap(u) => match &u.map {
                VelosiAstStaticMap::ListComp(m) => {
                    println!(
                        "{} - idx = (va >> {}) & 0x{:x}",
                        " ".repeat(indent + 2),
                        m.elm.dst_bitwidth,
                        (m.range.end - m.range.start) - 1
                    );
                    println!(
                        "{} - va' = va & 0x{:x}",
                        " ".repeat(indent + 2),
                        (1u64 << m.elm.dst_bitwidth) - 1
                    );
                    println!(
                        "{} - sz' = sz & 0x{:x}",
                        " ".repeat(indent + 2),
                        (1u64 << m.elm.dst_bitwidth) - 1
                    );
                }
                VelosiAstStaticMap::Explicit(_) => {
                    unimplemented!("handle explicit maps")
                }
                _ => {
                    unreachable!();
                }
            },
            Enum(_u) => {}
            OSSpec(_) => {}
        }

        if let Some(children) = self.relations.get(root.ident()) {
            for c in children.iter().rev() {
                //let indent = if !c.is_enum() { indent + 2 } else { indent };
                self.do_print_unit_hierarchy(c, indent + 2);
            }
        }
    }

    pub fn print_unit_hierarchy(&self, root: &VelosiAstUnit) {
        self.do_print_unit_hierarchy(root.ident(), 0);
    }
}

pub fn extract_composition(ast: &VelosiAst) {
    let units = ast.units();

    let mut all_units = HashSet::new();
    let mut referenced_units = HashSet::new();
    let mut relations = Relations::new();

    for unit in units {
        if unit.is_abstract() {
            continue;
        }

        all_units.insert(unit.ident().clone());

        use VelosiAstUnit::*;
        match unit {
            Segment(u) => {
                let mmap = u.get_method("map").unwrap();
                let next = mmap.get_param("pa").unwrap();
                if next.ptype.is_typeref() {
                    let f = next.ptype.typeref().unwrap().clone();
                    relations.insert(unit.clone(), vec![ast.get_unit(&f).unwrap().clone()]);
                    referenced_units.insert(f.clone());
                } else if !next.ptype.is_addr() {
                    unreachable!();
                }
            }
            StaticMap(u) => match &u.map {
                VelosiAstStaticMap::ListComp(m) => {
                    relations.insert(
                        unit.clone(),
                        vec![ast.get_unit(m.elm.dst.ident()).unwrap().clone()],
                    );
                    referenced_units.insert(m.elm.dst.ident().clone());
                }
                VelosiAstStaticMap::Explicit(_) => {
                    unimplemented!("handle explicit maps")
                }
                _ => {
                    unreachable!();
                }
            },
            Enum(u) => {
                for next in &u.get_next_unit_idents() {
                    relations.insert(unit.clone(), vec![ast.get_unit(next).unwrap().clone()]);
                    referenced_units.insert(Rc::new(next.to_string()));
                }
            }
            OSSpec(_) => {
                // nothing to be done here
            }
        }
    }

    let roots = all_units.sub(&referenced_units);

    println!("All units: {all_units:?}");
    println!("Referenced units: {referenced_units:?}");
    println!("Roots: {roots:?}");

    for root in &roots {
        println!("Root: {root:?}");
        relations.print_unit_hierarchy(ast.get_unit(root).unwrap());
    }
}

impl Default for Relations {
    fn default() -> Self {
        Self::new()
    }
}
