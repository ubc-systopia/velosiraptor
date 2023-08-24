/**
 * The Interface Base Class of the Translation Unit
 *
 * SPDX-License-Identifier: MIT
 *
 * Copyright (C) 2022, Reto Achermann (The University of British Columbia)
 */

#include <assert.h>

#include "logging.hpp"
#include "interface_base.hpp"


InterfaceBase::InterfaceBase(StateBase *state)
    : _state(state)
{
}


bool InterfaceBase::add_register(RegisterBase *reg)
{
    // TODO: do a proper overlap check...
    if (this->_register_by_addr.contains(reg->get_addr())) {
        Logging::error("InterfaceBase::add_register - register with address %lx already defined",
                       reg->get_addr());
        return false;
    }

    if (this->_register_by_name.contains(reg->get_name())) {
        Logging::error("InterfaceBase::add_register - register with name '%s' already defined",
                       reg->get_name().c_str());
        return false;
    }

    {
        auto r = this->_register_by_addr.insert(std::make_pair(reg->get_addr(), reg));
        assert(r.second);  // shouldn't fail
    }
    {
        auto r = this->_register_by_name.insert(std::make_pair(reg->get_name(), reg));
        assert(r.second);  // shouldn't fail
    }

    return true;
}

void InterfaceBase::reset(void)
{
    Logging::info("Resetting interface");
    for (auto &reg : this->_register_by_addr) {
        reg.second->reset();
    }
    Logging::info("Interface reset completed.");
}

void InterfaceBase::debug_print_interface(void)
{
    Logging::info("Interface Register Map:");
    for (auto it = this->_register_by_addr.begin(); it != this->_register_by_addr.end(); it++) {
        auto reg = it->second;
        reg->print_register();
    }
}

RegisterBase *InterfaceBase::lookup_register_by_name(const std::string &name)
{
    if (this->_register_by_name.contains(name)) {
        return this->_register_by_name.at(name);
    }

    Logging::error("Register with name %s not found", name.c_str());
    return nullptr;
}


RegisterBase *InterfaceBase::lookup_register_by_address(lpaddr_t addr)
{
    if (this->_register_by_addr.contains(addr)) {
        return this->_register_by_addr.at(addr);
    }

    Logging::error("Register with addr %llx not found", addr);
    return nullptr;
}


bool InterfaceBase::handle_register_write(RegisterBase *reg, uint8_t width, access_mode_t mode,
                                          uint64_t data)
{
    // check the access width (must match)
    if (reg->get_width() != width) {
        Logging::info("InterfaceBase::handle_register_write with unmatched width: %u (expected: "
                      "%u)",
                      width, reg->get_width());
        return false;
    }

    // write it!
    return reg->write(mode, data);
}

bool InterfaceBase::handle_register_write(lpaddr_t addr, uint8_t width, access_mode_t mode,
                                          uint64_t data)
{
    RegisterBase *reg = this->lookup_register_by_address(addr);
    if (reg == nullptr) {
        return false;
    }

    return this->handle_register_write(reg, width, mode, data);
}


bool InterfaceBase::handle_register_write(const std::string &name, uint8_t width,
                                          access_mode_t mode, uint64_t data)
{
    RegisterBase *reg = this->lookup_register_by_name(name);
    if (reg == nullptr) {
        return false;
    }

    return this->handle_register_write(reg, width, mode, data);
}


bool InterfaceBase::handle_register_read(RegisterBase *reg, uint8_t width, access_mode_t mode,
                                         uint64_t *data)
{
    // check the access width (must match)
    if (reg->get_width() != width) {
        Logging::info("InterfaceBase::handle_register_read with unmatched width: %u (expected: "
                      "%u)",
                      width, reg->get_width());
        return false;
    }

    // read it!
    return reg->read(mode, data);
}

bool InterfaceBase::handle_register_read(lpaddr_t addr, uint8_t width, access_mode_t mode,
                                         uint64_t *data)
{
    RegisterBase *reg = this->lookup_register_by_address(addr);
    if (reg == nullptr) {
        return false;
    }
    return this->handle_register_read(reg, width, mode, data);
}


bool InterfaceBase::handle_register_read(const std::string &name, uint8_t width,
                                         access_mode_t mode, uint64_t *data)
{
    RegisterBase *reg = this->lookup_register_by_name(name);
    if (reg == nullptr) {
        return false;
    }
    return this->handle_register_read(reg, width, mode, data);
}
