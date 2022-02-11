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
use std::io::BufWriter;
use std::io::Write;
use std::path::Path;
use std::path::PathBuf;

// other libraries
use crustal as CG;
use custom_error::custom_error;

// the lirbrary
use crate::ast::AstRoot;
use crate::hwgen::HWGenBackend;
use crate::hwgen::HWGenError;

// the generators
mod state;
use state::{generate_state_header, generate_state_impl};
mod interface;
use interface::{generate_interface_header, generate_interface_impl};
mod unit;
use unit::{generate_unit_header, generate_unit_impl};

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

impl ArmFastModelsModule {
    pub fn new(outdir: &Path, pkg: String) -> ArmFastModelsModule {
        // set the outpath to: outdir/fastmodels/<pkgname>
        let path = outdir.join("fastmodels");
        ArmFastModelsModule {
            outdir: path,
            pkgname: pkg,
        }
    }

    fn generate_makefile(&self) -> Result<(), HWGenError> {
        let makefile = File::create(self.outdir.join("Makefile"))?;
        let mut f = BufWriter::new(makefile);

        let lib = format!("lib{}.a", self.pkgname);

        writeln!(f, "# This file is auto-generated")?;

        // flags for the compiler
        writeln!(f, "\n# Set the build directory")?;
        writeln!(f, "BUILD_DIR := $(CURDIR)/build")?;
        writeln!(f, "SOURCE_DIR := $(CURDIR)")?;
        writeln!(f, "FRAMEWORK_DIR := $(CURDIR)")?;

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

        writeln!(f, "\n# Source Files")?;
        writeln!(f, "TRANSLATION_UNIT_SRCS := $(SOURCE_DIR)/unit.cpp")?;
        writeln!(f, "TRANSLATION_UNIT_SRCS += $(SOURCE_DIR)/interface.cpp")?;
        writeln!(f, "TRANSLATION_UNIT_SRCS += $(SOURCE_DIR)/state.cpp")?;
        writeln!(f, "TRANSLATION_UNIT_SRCS += $(SOURCE_DIR)/registers.cpp")?;

        writeln!(f, "\n# Object Files")?;
        writeln!(
            f,
            "TRANSLATION_UNIT_OBJS := $(TRANSLATION_UNIT_SRCS:src/%.cpp=$(BUILD_DIR)/objs/%.o)"
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

        // other rules
        writeln!(f, "\n# clean up")?;
        writeln!(f, "clean:")?;
        writeln!(f, "\trm -rf $(BUILD_DIR)")?;

        f.flush()?;

        Ok(())
    }
}

impl HWGenBackend for ArmFastModelsModule {
    fn prepare(&self) -> Result<(), HWGenError> {
        // outdir/hw/fastmodels/<pkgname>/include
        let includedir = self.outdir.join("include");

        // create the package path
        fs::create_dir_all(includedir)?;

        Ok(())
    }

    /// generates the unit
    fn generate_unit(&self, ast: &AstRoot) -> Result<(), HWGenError> {
        generate_unit_header(&self.outdir).expect("failed to generate the unit header");
        generate_unit_impl(&self.outdir).expect("failed to generate the unit implementation");
        Ok(())
    }

    /// generate the interface definitions
    fn generate_interface(&self, ast: &AstRoot) -> Result<(), HWGenError> {
        generate_interface_header(&self.outdir).expect("failed to generate the interface header");
        generate_interface_impl(&self.outdir)
            .expect("failed to generate the interface implementation");
        Ok(())
    }

    /// generates the state representation
    fn generate_state(&self, ast: &AstRoot) -> Result<(), HWGenError> {
        println!("GENERATING THE STATE!");

        if !ast.units.is_empty() {
            generate_state_header(&self.pkgname, &ast.units[0].state, &self.outdir)
                .expect("failed to generate the state header");
            generate_state_impl(&self.pkgname, &ast.units[0].state, &self.outdir)
                .expect("failed to generate the state implementation");
        }

        Ok(())
    }

    /// finalizes the code generation part
    fn finalize(&self) -> Result<(), HWGenError> {
        self.generate_makefile()
    }
}
