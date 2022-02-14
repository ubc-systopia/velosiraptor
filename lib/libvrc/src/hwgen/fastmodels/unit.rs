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

//! # The FastModels Platform Generator: State
//!
//! This module generates the unit description of the Arm FastModels implementation
//! of the translation unit.

// the path buffer
use std::path::Path;

// other libraries
use crustal as C;
use custom_error::custom_error;

// the defined errors
use crate::ast::Unit;
use crate::hwgen::fastmodels::interface::to_interface_class_name;
use crate::hwgen::fastmodels::state::to_state_class_name;
use crate::hwgen::HWGenError;

pub fn to_unit_class_name(name: &str) -> String {
    format!("{}{}Unit", name[0..1].to_uppercase(), &name[1..])
}

fn add_constructor(c: &mut C::Class, ifn: &str, scn: &str) {
    // TranslationUnit::TranslationUnit(std::string const                     &name,
    //                                  pv::RandomContextTransactionGenerator *ptw_pvbus)
    //     : TranslationUnitBase(name, ptw_pvbus, 0, CONFIG_END_ADDRESS)
    //     , _state(TranslationUnitState())
    //     , _interface(TranslationUnitInterface(&_state))
    // {
    // }
    //     TranslationUnit(std::string const                     &name,
    //     pv::RandomContextTransactionGenerator *ptw_pvbus = nullptr);
    let mut arg0_type = C::Type::new_std_string();
    arg0_type.constant().reference();

    let mut arg1_type = C::Type::new_class("pv::RandomContextTransactionGenerator");
    arg1_type.pointer();

    c.new_constructor()
        .private()
        .push_argument(C::MethodParam::new("name", arg0_type))
        .push_parent_initializer(C::Expr::fn_call("TranslationUnitBase", vec![/* TOOD */]))
        .push_initializer("_state", C::Expr::fn_call(scn, vec![]))
        .push_initializer("_interface", C::Expr::fn_call(ifn, vec![]))
        .new_argument("ptw_pvbus", arg1_type)
        .default("nullptr");
}

fn add_create(c: &mut C::Class, ucn: &str) {
    // static TranslationUnit *create(sg::ComponentBase *parentComponent, std::string const &name,
    //     sg::CADIBase                          *cadi,
    //     pv::RandomContextTransactionGenerator *ptw_pvbus);
    // TODO: finish

    let unit_ptr_type = C::Type::from_ptr(&C::Type::new_class(ucn));

    let mut m = c.new_method("create", unit_ptr_type).public().sstatic();

    let mut arg0_type = C::Type::new_class("sg::ComponentBase");
    arg0_type.pointer();

    let mut arg1_type = C::Type::new_std_string();
    arg1_type.constant().reference();

    let mut arg2_type = C::Type::new_class("sg::CADIBase ");
    arg2_type.pointer();

    let mut arg3_type = C::Type::new_class("pv::RandomContextTransactionGenerator");
    arg3_type.pointer();

    // arguments
    m.push_argument(C::MethodParam::new("parentComponent", arg0_type))
        .push_argument(C::MethodParam::new("name", arg1_type))
        .push_argument(C::MethodParam::new("cadi", arg2_type))
        .push_argument(C::MethodParam::new("ptw_pvbus", arg3_type));

    // body
    let unitvar = C::Stmt::localvar("t", C::Type::new_class(ucn));

    m.push_stmt(unitvar)
    .push_stmt(C::Stmt::fn_call(C::Expr::fn_call(
        "Logging::debug",
        vec![C::Expr::new_str("Register::do_read()")],
    )))


     ;


    ;

    // TranslationUnit *TranslationUnit::create(sg::ComponentBase *parentComponent,
    //                                          std::string const &name, sg::CADIBase *cadi,
    //                                          pv::RandomContextTransactionGenerator *ptw_pvbus)
    // {
    //     Logging::debug("creating new translation unit.\n");

    //     TranslationUnit *t = new TranslationUnit(name, ptw_pvbus);

    //     t->_state.print_state_fields();
    //     t->_interface.debug_print_interface();

    //     Logging::debug("translation unit created.\n");

    //     return t;
    // }
}

fn add_translate(c: &mut C::Class, ifn: &str, scn: &str) {
    // virtual bool do_translate(lvaddr_t src_addr, size_t size, access_mode_t mode,
    // lpaddr_t *dst_addr) override;

    let src_addr_param = C::MethodParam::new("src_addr", C::Type::new_typedef("lvaddr_t"));
    let size_param = C::MethodParam::new("size", C::Type::new_size());
    let mode_param = C::MethodParam::new("mode", C::Type::new_typedef("access_mode_t"));
    let dst_addr_param = C::MethodParam::new(
        "dst_addr",
        C::Type::from_ptr(&C::Type::new_typedef("lpaddr_t")),
    );
    c.new_method("do_translate", C::Type::from_ptr(&C::Type::new_bool()))
        .public()
        .virt()
        .overrid()
        .push_argument(src_addr_param)
        .push_argument(size_param)
        .push_argument(mode_param)
        .push_argument(dst_addr_param);

    // bool TranslationUnit::do_translate(lvaddr_t src_addr, size_t size, access_mode_t mode,
    //                                    lpaddr_t *dst_addr)
    // {
    //     Logging::debug("TranslationUnit::do_translate()");

    //     auto ctrl = this->_state.control_field();
    //     if (!(ctrl->get_value() & 0x1)) {
    //         Logging::debug("TranslationUnit::translate() - disabled. don't remap. %x");
    //         *dst_addr = src_addr;
    //         return true;
    //     }

    //     size_t idx    = src_addr / CONFIG_TRANSLATION_BLOCK_SIZE;
    //     size_t offset = src_addr % CONFIG_TRANSLATION_BLOCK_SIZE;

    //     assert(idx < CONFIG_NUM_TRANSLATION_REGISTERS);

    //     lpaddr_t segbase = this->_state.get_base_field_n_value(idx);
    //     size_t   segsize = this->_state.get_size_field_n_value(idx);

    //     if (offset >= segsize) {
    //         Logging::debug("TranslationUnit::translate() - offset >= size ", src_addr, size);
    //         return false;
    //     }

    //     if (idx >= CONFIG_NUM_TRANSLATION_REGISTERS) {
    //         Logging::debug("TranslationUnit::translate() - idx %zu >= "
    //                        "CONFIG_NUM_TRANSLATION_REGISTERS %u",
    //                        idx, CONFIG_NUM_TRANSLATION_REGISTERS);
    //         return false;
    //     }

    //     // set the return address
    //     *dst_addr = segbase + offset;

    //     return true;
    // }
}

pub fn generate_unit_header(name: &str, unit: &Unit, outdir: &Path) -> Result<(), HWGenError> {
    let mut scope = C::Scope::new();
    scope.set_filename("include/unit.hpp");

    let ifn = to_interface_class_name(name);
    let scn = to_state_class_name(name);
    let ucn = to_unit_class_name(name);

    scope.push_doc_str(format!("The Unit of the '{}' Translation Unit\n\n", scn).as_str());
    scope.push_doc_str("WARNING: This file is auto-generated by the  Velosiraptor compiler.\n");

    // set the header guard
    let guard = scope.new_ifdef(format!("{}_UNIT_HPP_", name.to_uppercase()).as_str());

    // create the scope guard
    let s = guard.guard().then_scope();

    s.new_comment("system includes");
    s.new_include("string.h", true);
    s.new_include("assert.h", true);

    s.new_comment("framework includes");
    s.new_include("generic/types.hpp", true);
    s.new_include("generic/translation_unit_base.hpp", true);

    s.new_comment("translation unit specific includes");
    s.new_include("state.hpp", true);
    s.new_include("interface.hpp", true);

    // create a new class in the scope
    let c = s.new_class(ucn.as_str());

    c.set_base("TranslationUnitBase", C::Visibility::Public);

    add_constructor(c, &ifn, &scn);
    add_create(c, &ucn);
    add_translate(c, &ifn, &scn);

    //
    // virtual UnitBase *get_interface(void) override
    // {
    //     return &this->_interface;
    // }
    c.new_method(
        "get_interface",
        C::Type::from_ptr(&C::Type::new_class("UnitBase")),
    )
    .public()
    .virt()
    .inside_def()
    .overrid()
    .push_stmt(C::Stmt::retval(C::Expr::addr_of(&C::Expr::field_access(
        &C::Expr::this(),
        "_interface",
    ))));

    //
    // virtual StateBase *get_state(void) override
    // {
    //     return &this->_state;
    // }
    c.new_method(
        "get_state",
        C::Type::from_ptr(&C::Type::new_class("StateBase")),
    )
    .public()
    .virt()
    .overrid()
    .inside_def()
    .push_stmt(C::Stmt::retval(C::Expr::addr_of(&C::Expr::field_access(
        &C::Expr::this(),
        "_state",
    ))));

    // attributes

    let state_ptr_type = C::Type::from_ptr(&C::Type::new_class(&scn));
    let iface_ptr_type = C::Type::from_ptr(&C::Type::new_class(&ifn));

    // add the state attribute
    c.new_attribute("_state", state_ptr_type);
    c.new_attribute("_interface", iface_ptr_type);

    // TODO: handle the methods!
    for m in &unit.methods {
        println!("handle method {}!", m.name);
    }

    // save the scope
    scope.to_file(outdir, true)?;

    Ok(())
}

pub fn generate_unit_impl(name: &str, unit: &Unit, outdir: &Path) -> Result<(), HWGenError> {
    let mut scope = C::Scope::new();
    scope.set_filename("unit.cpp");

    let ifn = to_interface_class_name(name);
    let scn = to_state_class_name(name);
    let ucn = to_unit_class_name(name);

    scope.push_doc_str(format!("The Unit of the '{}' Translation Unit\n\n", scn).as_str());
    scope.push_doc_str("WARNING: This file is auto-generated by the  Velosiraptor compiler.\n");

    scope.new_comment("system includes");
    scope.new_include("string.h", true);
    scope.new_include("assert.h", true);

    scope.new_comment("framework includes");
    scope.new_include("generic/types.hpp", true);
    scope.new_include("generic/logging.hpp", true);

    scope.new_comment("translation unit specific includes");
    scope.new_include("unit.hpp", true);
    scope.new_include("interface.hpp", true);

    // create a new class in the scope
    let c = scope.new_class(ucn.as_str());

    c.set_base("TranslationUnitBase", C::Visibility::Public);

    add_constructor(c, &ifn, &scn);
    add_translate(c, &ifn, &scn);
    add_create(c, &ucn);

    /*
     * -------------------------------------------------------------------------------------------
     * Translations
     * -------------------------------------------------------------------------------------------
     */

    // TODO: handle the methods!
    for m in &unit.methods {
        println!("handle method {}!", m.name);
    }

    scope.to_file(outdir, false)?;

    Ok(())
}
