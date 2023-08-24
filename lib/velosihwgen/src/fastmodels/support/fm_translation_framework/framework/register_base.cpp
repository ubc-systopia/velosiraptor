/**
 * The Register Base Class of the Translation Unit
 *
 * SPDX-License-Identifier: MIT
 *
 * Copyright (C) 2022, Reto Achermann (The University of British Columbia)
 */

#include <string.h>

#include "logging.hpp"
#include "register_base.hpp"


RegisterBase::RegisterBase(std::string name, lpaddr_t addr, uint8_t width, access_perms_t perms,
                           uint64_t reset_value, StateBase *state)
    : _name(name)
    , _idx(0)
    , _addr(addr)
    , _perms(perms)

{
    switch (width) {
    case 1:
        this->_value_mask = 0xff;
        break;
    case 2:
        this->_value_mask = 0xffff;
        break;
    case 4:
        this->_value_mask = 0xffffffff;
        break;
    case 8:
        this->_value_mask = 0xffffffffffffffff;
        break;
    default:
        Logging::panic("RegisterBase::RegisterBase: invalid width %d\n", width);
    }

    this->_width       = width;
    this->_reset_value = reset_value;
    this->_state       = state;
}


RegisterBase::RegisterBase(std::string name, size_t idx, lpaddr_t addr, uint8_t width,
                           access_perms_t perms, uint64_t reset_value, StateBase *state)
    : RegisterBase(RegisterBase::mk_idx_name(name, idx), addr, width, perms, reset_value, state)
{
    this->_idx = idx;
}


RegisterBase::~RegisterBase(void) { }


void RegisterBase::print_register(void)
{
    Logging::info("  %16s  0x%016lx..0x%016lx (%u)  init=0x%016lx   %lx", this->_name.c_str(),
                  this->_addr, this->_addr + this->_width - 1, this->_width, this->_reset_value,
                  this->_perms);
}

std::string RegisterBase::mk_idx_name(std::string name, size_t idx)
{
    name.push_back('_');

    char buf[9];
    snprintf(buf, 9, "%zu", idx);
    name += buf;

    return name;
}

bool RegisterBase::write(access_mode_t mode, uint64_t data)
{
    if (this->check_access_mode(mode)) {
        Logging::debug("RegisterBase::write(%s, %zu) = 0x%lx", this->_name.c_str(), this->_idx,
                       data);
        // check if the data has invalid bits set
        if (data & ~(this->_value_mask)) {
            Logging::warn("%s::write: value written has unsupported values. 0x%lx (0x%lx)\n",
                          this->_name, data, data & this->_value_mask);
        }

        // mask the valid bits
        data = data & this->_value_mask;

        // call the write function
        this->do_write(data);
        return true;
    }
    Logging::info("RegisterBase::write(%s, %zu) = access mode violation (%x %x)",
                  this->_name.c_str(), this->_idx, mode, this->_perms);
    return false;
}

bool RegisterBase::read(access_mode_t mode, uint64_t *data)
{
    if (this->check_access_mode(mode)) {
        // call the write function
        Logging::debug("RegisterBase::read(%s, %zu)", this->_name.c_str(), this->_idx);
        *data = this->do_read() & this->_value_mask;
        return true;
    }
    Logging::info("RegisterBase::read(%s, %zu) - Access mode violation", this->_name.c_str(),
                  this->_idx);
    return false;
}

// default implementation of the read action
uint64_t RegisterBase::do_read()
{
    Logging::debug("RegisterBase::do_read()");
    return this->_value;
}

// default implementation of the write action
void RegisterBase::do_write(uint64_t data)
{
    Logging::debug("RegisterBase::do_write(0x%lx)", data);
    this->_value = data;
}
