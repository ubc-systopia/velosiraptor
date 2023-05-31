// Velosiraptor Compiler
//
//
// MIT License
//
// Copyright (c) 2022 The University of British Columbia, Vancouver, BC, Canada
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

//! # The FastModels Platform Generator
//!
//! This module contains a generator for a Arm FastModels component.

// the used external libraries
use std::fs;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};

// other libraries
use crustal as C;

// the library
use velosiast::VelosiAst;
use crate::VelosiHwGenBackend;
use crate::VelosiHwGenError;
use crate::COPYRIGHT;

// the generators
mod state;
use state::{generate_state_header, generate_state_impl, state_impl_file};
mod interface;
use interface::{generate_interface_header, generate_interface_impl, interface_impl_file};
mod unit;
use unit::{generate_unit_header, generate_unit_impl, unit_impl_file};
mod registers;
use registers::{generate_register_header, generate_register_impl, registers_impl_file};
mod fields;
use fields::{generate_field_header, generate_field_impl, state_fields_impl_file};

/// # The Arm FastModels Platform Module
///
/// This generator produces a component for the Arm FastModels simulator using the
/// `TranslationUnit` support library.
///
/// ## Generated File Structure
///
///  - outdir/hw/fastmodels/<pkgname>
///  - outdir/hw/fastmodels/<pkgname>/include
///  - outdir/hw/fastmodels/<pkgname>/include/registers.hpp
///  - outdir/hw/fastmodels/<pkgname>/include/interface.hpp
///  - outdir/hw/fastmodels/<pkgname>/include/state.hpp
///  - outdir/hw/fastmodels/<pkgname>/include/unit.hpp
///  - outdir/hw/fastmodels/<pkgname>/registers.cpp
///  - outdir/hw/fastmodels/<pkgname>/unit.cpp
///  - outdir/hw/fastmodels/<pkgname>/interface.cpp
///  - outdir/hw/fastmodels/<pkgname>/state.cpp

///
pub struct ArmFastModelsModule {
    outdir: PathBuf,
    pkgname: String,
}

pub fn add_header(scope: &mut C::Scope, unit: &str, comp: &str) {
    scope.push_doc_str(format!("The {} of the '{}' translation unit\n\n", comp, unit).as_str());
    scope.push_doc_str(COPYRIGHT);
    scope.push_doc_str("WARNING: This file is auto-generated by the Velosiraptor compiler.\n");
}

impl ArmFastModelsModule {
    pub fn new(outdir: &Path, pkg: String) -> ArmFastModelsModule {
        // set the outpath to: outdir/fastmodels/<pkgname>
        let path = outdir.join("fastmodels");
        ArmFastModelsModule {
            outdir: path,
            pkgname: pkg,
        }
    }

    fn generate_makefile(&self, name: &str) -> Result<(), VelosiHwGenError> {
        let makefile = File::create(self.outdir.join("Makefile"))?;
        let mut f = BufWriter::new(makefile);

        let lib = format!("lib{}.a", self.pkgname);

        writeln!(f, "# This file is auto-generated")?;

        // flags for the compiler
        writeln!(f, "\n# Set the build directory")?;
        writeln!(f, "BUILD_DIR := $(CURDIR)/build")?;
        writeln!(f, "SOURCE_DIR := $(CURDIR)")?;
        writeln!(f, "FRAMEWORK_DIR ?= $(CURDIR)/framework")?;

        // flags for the compiler
        writeln!(f, "# compiler flags")?;
        writeln!(f, "CC      := g++")?;
        writeln!(f, "CCFLAGS := -Wall -O3 -Werror -std=c++20 -fPIC")?;
        writeln!(f, "CCFLAGS += -I include")?;
        writeln!(f, "CCFLAGS += -I $(FRAMEWORK_DIR)/include")?;
        writeln!(f, "CCFLAGS += -I $(PVLIB_HOME)/include")?;
        writeln!(f, "CCFLAGS += -I $(PVLIB_HOME)/include/fmruntime")?;
        writeln!(f, "CCFLAGS += -MMD -MP")?;

        // flags for creating the static library
        writeln!(f, "# archive flags")?;
        writeln!(f, "AR      := ar")?;
        writeln!(f, "ARFLAGS := rcs")?;

        // creating directories
        writeln!(f, "# creating directories")?;
        writeln!(f, "MKDIR := mkdir -p")?;

        writeln!(f, "\n# Source Files")?;
        writeln!(
            f,
            "TRANSLATION_UNIT_SRCS := $(SOURCE_DIR)/{}",
            unit_impl_file(name)
        )?;
        writeln!(
            f,
            "TRANSLATION_UNIT_SRCS += $(SOURCE_DIR)/{}",
            interface_impl_file(name)
        )?;
        writeln!(
            f,
            "TRANSLATION_UNIT_SRCS += $(SOURCE_DIR)/{}",
            state_impl_file(name)
        )?;
        writeln!(
            f,
            "TRANSLATION_UNIT_SRCS += $(SOURCE_DIR)/{}",
            registers_impl_file(name)
        )?;
        writeln!(
            f,
            "TRANSLATION_UNIT_SRCS += $(SOURCE_DIR)/{}",
            state_fields_impl_file(name)
        )?;

        writeln!(f, "\n# Object Files")?;
        writeln!(
            f,
            "TRANSLATION_UNIT_OBJS := $(TRANSLATION_UNIT_SRCS:$(SOURCE_DIR)/%.cpp=$(BUILD_DIR)/objs/%.o)"
        )?;

        writeln!(f, "\n# The Translation Unit Library")?;
        writeln!(f, "TRANSLATION_UNIT_LIB  := $(BUILD_DIR)/{}", lib)?;

        // rule to build the library
        writeln!(f, "\n# building the library")?;
        writeln!(f, "$(TRANSLATION_UNIT_LIB): $(TRANSLATION_UNIT_OBJS)")?;
        writeln!(f, "\t$(MKDIR) $(@D)")?;
        writeln!(f, "\t$(AR) $(ARFLAGS) -o $@ $^")?;

        writeln!(f, "\n# Targets")?;
        writeln!(f, ".DEFAULT_GOAL = all")?;
        writeln!(f, "all: $(TRANSLATION_UNIT_LIB)")?;

        // compilation rules
        writeln!(f, "\n# Compilation Rules")?;
        writeln!(f, "$(BUILD_DIR)/objs/%.o: $(SOURCE_DIR)/%.cpp")?;
        writeln!(f, "\t$(MKDIR) $(@D)")?;
        writeln!(f, "\t$(CC) $(CCFLAGS) -c -o $@ $<")?;

        // other rules
        writeln!(f, "\n# clean up")?;
        writeln!(f, "clean:")?;
        writeln!(f, "\trm -rf $(BUILD_DIR)")?;

        f.flush()?;

        Ok(())
    }
}

impl VelosiHwGenBackend for ArmFastModelsModule {
    fn prepare(&self, ast: &VelosiAst) -> Result<(), VelosiHwGenError> {
        // outdir/hw/fastmodels/<pkgname>/<unitname>/include
        for u in ast.units() {
            let out_subdir = &self.outdir.join(u.ident_to_string());
            fs::create_dir_all(out_subdir)?;
            let includedir = out_subdir.join("include");
            fs::create_dir_all(includedir)?;
        }
        Ok(())
    }

    fn generate_units(&self, ast: &VelosiAst) -> Result<(), VelosiHwGenError> {
        for u in ast.units() {
            let out_subdir = &self.outdir.join(u.ident_to_string());
            generate_unit_header(&self.pkgname, u, out_subdir)
                .expect("failed to generate the unit header");
            generate_unit_impl(&self.pkgname, u, out_subdir)
                .expect("failed to generate the unit implementation");
        };
        Ok(())
    }

    /// generate the interface definitions
    fn generate_interfaces(&self, ast: &VelosiAst) -> Result<(), VelosiHwGenError> {
        for u in ast.units() {
            let out_subdir = &self.outdir.join(u.ident_to_string());
            match &u.interface() {
                None => (),
                Some(i) => {
                    generate_register_header(&self.pkgname, i, out_subdir)
                        .expect("failed to generate the interface header");
                    generate_register_impl(&self.pkgname, i, out_subdir)
                        .expect("failed to generate the interface header");
                    generate_interface_header(&self.pkgname, i, out_subdir)
                        .expect("failed to generate the interface header");
                    generate_interface_impl(&self.pkgname, i, out_subdir)
                        .expect("failed to generate the interface implementation");
                }
            }
        }
        Ok(())
    }

    /// generates the state representation
    fn generate_states(&self, ast: &VelosiAst) -> Result<(), VelosiHwGenError> {
        for u in ast.segments() {
            let out_subdir = &self.outdir.join(u.ident_to_string());
            generate_field_header(&self.pkgname, &u.state, out_subdir)
                .expect("failed to generate the fields header");
            generate_field_impl(&self.pkgname, &u.state, out_subdir)
                .expect("failed to generate the fields implementation");
            generate_state_header(&self.pkgname, &u.state, out_subdir)
                .expect("failed to generate the state header");
            generate_state_impl(&self.pkgname, &u.state, out_subdir)
                .expect("failed to generate the state implementation");
        }

        Ok(())
    }

    /// finalizes the code generation part
    fn finalize(&self) -> Result<(), VelosiHwGenError> {
        self.generate_makefile(&self.pkgname)
    }
}
