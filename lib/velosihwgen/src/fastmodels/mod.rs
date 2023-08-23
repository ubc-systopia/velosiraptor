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
use crate::VelosiHwGenBackend;
use crate::VelosiHwGenError;
use crate::COPYRIGHT;
use velosiast::VelosiAst;

// the generators
mod state;
use state::{generate_state_header, generate_state_impl, state_impl_file};
mod interface;
use interface::{generate_interface_header, generate_interface_impl, interface_impl_file};
mod unit;
use unit::generate_unit_header;
mod registers;
use registers::{generate_register_header, generate_register_impl};

use self::unit::unit_header_file;

/// # The Arm FastModels Platform Module
///
/// This generator produces a component for the Arm FastModels simulator using the
/// `TranslationUnit` support library.
///
/// ## Generated File Structure
///
/// main makefile will call all unit makefiles
///  - outdir/hw/fastmodels/Makefile
///
/// for unit in vrs:
///  - outdir/hw/fastmodels/<unit>/
///  - outdir/hw/fastmodels/<unit>/Makefile
///  - outdir/hw/fastmodels/<unit>/<unit>_interface.hpp
///  - outdir/hw/fastmodels/<unit>/<unit>_interface.cpp
///  - outdir/hw/fastmodels/<unit>/<unit>_state.hpp
///  - outdir/hw/fastmodels/<unit>/<unit>_state.cpp
///  - outdir/hw/fastmodels/<unit>/<unit>_unit.hpp
///  - outdir/hw/fastmodels/<vrs>_registers.cpp
///  - outdir/hw/fastmodels/<vrs>_registers.hpp
///
///  Fastmodels framework lib is adjacent to units
///  note no unit can share the name of the framework folder
///  - outdir/hw/fastmodels/fm-translation-framework/
///  - outdir/hw/fastmodels/fm-translation-framework/accessmode.hpp
///  - outdir/hw/fastmodels/fm-translation-framework/interface_base.hpp
///  - outdir/hw/fastmodels/fm-translation-framework/logging.hpp
///  - outdir/hw/fastmodels/fm-translation-framework/register_base.hpp
///  - outdir/hw/fastmodels/fm-translation-framework/state_base.hpp
///  - outdir/hw/fastmodels/fm-translation-framework/state_field_base.hpp
///  - outdir/hw/fastmodels/fm-translation-framework/translation_unit_base.hpp
///  - outdir/hw/fastmodels/fm-translation-framework/types.hpp

pub struct ArmFastModelsModule {
    outdir: PathBuf,
    fdir: String, // relative to outdir
    pkgname: String,
}

pub fn add_header_comment(scope: &mut C::Scope, unit: &str, comp: &str) {
    scope.push_doc_str(format!("The {} of the '{}' translation unit\n\n", comp, unit).as_str());
    scope.push_doc_str(COPYRIGHT);
    scope.push_doc_str("WARNING: This file is auto-generated by the Velosiraptor compiler.\n");
}

impl ArmFastModelsModule {
    pub fn new(hwdir: &Path, pkgname: String) -> ArmFastModelsModule {
        ArmFastModelsModule {
            outdir: hwdir.join("fastmodels"),
            fdir: "fm_translation_framework".to_string(),
            pkgname,
        }
    }

    fn generate_top_makefile(&self, ast: &VelosiAst) -> Result<(), VelosiHwGenError> {
        let makefile = File::create(&self.outdir.join("Makefile"))?;
        let mut f = BufWriter::new(makefile);

        writeln!(f, "# This file is auto-generated\n")?;

        writeln!(
            f,
            "FRAMEWORK_URL=https://github.com/mlechu/arm-fastmodels-translation-framework",
        )?;
        writeln!(
            f,
            "FRAMEWORK_COMMIT=ef7c98835cdcc3a57a9ffda813bfc6d4feeddd53",
        )?;
        writeln!(f, "FRAMEWORK_DIR={}", self.fdir)?;

        writeln!(f, "\nall: deps_framework")?;
        writeln!(f, "\tmake -C {}", self.fdir)?;
        for u in ast.units() {
            if u.is_abstract() {
                continue;
            }
            // writeln!(f, "\tmake -d -I framework/build/include -C {}", u.ident())?;
            writeln!(f, "\tmake -C {}", u.ident())?;
        }

        writeln!(f, "deps_framework:")?;
        writeln!(f, "\t!(test -s $(FRAMEWORK_DIR)/.git) &&\\")?;
        writeln!(f, "\tgit clone $(FRAMEWORK_URL) $(FRAMEWORK_DIR);\\")?;
        writeln!(f, "\tgit -C $(FRAMEWORK_DIR) fetch;\\")?;
        writeln!(f, "\tgit -C $(FRAMEWORK_DIR) checkout $(FRAMEWORK_COMMIT)")?;

        writeln!(f, "\nclean:")?;
        writeln!(f, "\trm -rf {}", self.fdir)?;

        f.flush()?;

        Ok(())
    }

    fn generate_unit_makefile(&self, name: &str, out: &Path) -> Result<(), VelosiHwGenError> {
        let makefile = File::create(out.join("Makefile"))?;
        let mut f = BufWriter::new(makefile);

        let lib = format!("lib{}.a", self.pkgname);

        writeln!(f, "# This file is auto-generated")?;

        // flags for the compiler
        writeln!(f, "\n# Set the build directory")?;
        writeln!(f, "BUILD_DIR := $(CURDIR)/build")?;
        writeln!(f, "SOURCE_DIR := $(CURDIR)")?;
        writeln!(f, "FRAMEWORK_DIR ?= $(CURDIR)/../{}", self.fdir)?;

        writeln!(f, "# compiler flags")?;
        writeln!(
            f,
            "# PVLIB_HOME should be set by the fastmodels setup script"
        )?;
        writeln!(f, "CC      := g++")?;
        writeln!(f, "CCFLAGS := -Wall -O3 -Werror -std=c++2a -fPIC")?;

        // should probably include something from frameworkdir/build/(?)
        writeln!(f, "CCFLAGS += -I $(FRAMEWORK_DIR)")?;
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
            unit_header_file(name)
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
        // outdir/hw/fastmodels/<pkgname>/<unitname>
        for u in ast.units() {
            if u.is_abstract() {
                continue;
            }
            let out_subdir = &self.outdir.join(u.ident_to_string());
            fs::create_dir_all(out_subdir)?;
        }
        Ok(())
    }

    fn generate(&self, ast: &VelosiAst) -> Result<(), VelosiHwGenError> {
        // check all units for registers and put them in the main directory
        generate_register_header(&self.pkgname, ast, &self.outdir)?;
        generate_register_impl(&self.pkgname, ast, &self.outdir)?;

        for u in ast.units() {
            if u.is_abstract() {
                continue;
            }

            // let unit_dir = &self.outdir.join(u.ident_to_string());

            generate_unit_header(u, &self.outdir)?;
            // generate_interface_header(&self.pkgname, u, unit_dir)?;
            // generate_interface_impl(&self.pkgname, u, unit_dir)?;
            // generate_state_header(u, unit_dir)?;
            // generate_state_impl(u, unit_dir)?;
        }
        Ok(())
    }

    fn finalize(&self, ast: &VelosiAst) -> Result<(), VelosiHwGenError> {
        for u in ast.units() {
            if u.is_abstract() {
                continue;
            }

            let out_subdir = &self.outdir.join(u.ident_to_string());

            self.generate_unit_makefile(&u.ident_to_string(), out_subdir)
                .expect("Could not generate makefile");
        }
        self.generate_top_makefile(ast)
            .expect("Could not generate makefile");
        Ok(())
    }
}
