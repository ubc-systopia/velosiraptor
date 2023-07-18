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

use velosiast::ast::{VelosiAstStaticMap, VelosiAstUnit};
use velosiast::VelosiAst;

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

//pub struct Relation(pub Rc<String>, pub Rc<String>);
pub struct Relations(pub HashMap<Rc<String>, Vec<VelosiAstUnit>>);
impl Relations {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn from_ast(ast: &VelosiAst) -> Self {
        let units = ast.units();
        let mut relations = Self::new();

        for unit in units {
            if unit.is_abstract() {
                continue;
            }

            use VelosiAstUnit::*;
            match unit {
                Segment(u) => {
                    let mmap = u.get_method("map").unwrap();
                    let next = mmap.get_param("pa").unwrap();
                    if next.ptype.is_typeref() {
                        let f = next.ptype.typeref().unwrap().clone();
                        relations.insert(u.ident().clone(), ast.get_unit(&f).unwrap().clone());
                    } else if !next.ptype.is_addr() {
                        unreachable!();
                    }
                }
                StaticMap(u) => match &u.map {
                    VelosiAstStaticMap::ListComp(m) => {
                        relations.insert(
                            u.ident().clone(),
                            ast.get_unit(m.elm.dst.ident()).unwrap().clone(),
                        );
                    }
                    VelosiAstStaticMap::Explicit(_) => {
                        unimplemented!("handle explicit maps")
                    }
                    _ => {
                        unreachable!();
                    }
                },
                Enum(u) => {
                    for next in &u.get_unit_names() {
                        relations.insert(u.ident().clone(), ast.get_unit(next).unwrap().clone());
                    }
                }
            }
        }

        relations
    }

    pub fn insert(&mut self, key: Rc<String>, value: VelosiAstUnit) {
        let entry = self.0.entry(key).or_insert_with(Vec::new);
        entry.push(value);
    }

    fn do_print_unit_hierarchy(&self, root: &VelosiAstUnit, indent: usize) {
        use VelosiAstUnit::*;
        let prefix = match root {
            Segment(_u) => "~ ",
            StaticMap(_u) => {
                println!();
                "# "
            }
            Enum(_u) => "",
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
        }

        if let Some(children) = self.0.get(root.ident()) {
            for c in children.iter().rev() {
                //let indent = if !c.is_enum() { indent + 2 } else { indent };
                self.do_print_unit_hierarchy(c, indent + 2);
            }
        }
    }

    pub fn print_unit_hierarchy(&self, root: &VelosiAstUnit) {
        self.do_print_unit_hierarchy(root, 0);
    }
}

use std::collections::{HashMap, HashSet};

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
                    relations.insert(u.ident().clone(), ast.get_unit(&f).unwrap().clone());
                    referenced_units.insert(f.clone());
                } else if !next.ptype.is_addr() {
                    unreachable!();
                }
            }
            StaticMap(u) => match &u.map {
                VelosiAstStaticMap::ListComp(m) => {
                    relations.insert(
                        u.ident().clone(),
                        ast.get_unit(m.elm.dst.ident()).unwrap().clone(),
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
                for next in &u.get_unit_names() {
                    relations.insert(u.ident().clone(), ast.get_unit(next).unwrap().clone());
                    referenced_units.insert(Rc::new(next.to_string()));
                }
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
