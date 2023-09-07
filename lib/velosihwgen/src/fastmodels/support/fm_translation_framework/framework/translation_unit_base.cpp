/**
 * Translation Unit Base class implementation
 *
 * SPDX-License-Identifier: MIT
 *
 * Copyright (C) 2022, Reto Achermann (The University of British Columbia)
 */

#include "pv/PVBusMaster.h"
#include "pv/PVAccessWidth.h"

#include "translation_unit_base.hpp"
#include "interface_base.hpp"
#include "logging.hpp"
#include <streambuf>

/*
 * -------------------------------------------------------------------------------------------
 * Reset
 * -------------------------------------------------------------------------------------------
 */

void TranslationUnitBase::reset(void)
{
    Logging::info("resetting translation unit '%s'", this->_name.c_str());
    this->get_state()->reset();
    this->get_interface()->reset();
    Logging::info("reset completed");
}

void TranslationUnitBase::set_reset(bool signal_level) { }


/*
 * -------------------------------------------------------------------------------------------
 * Printing Functionality
 * -------------------------------------------------------------------------------------------
 */

// prints the global state
std::ostream &TranslationUnitBase::print_global_state(std::ostream &os)
{
    return os;
}

// prints the translation steps for an address
std::ostream &TranslationUnitBase::print_translation(std::ostream &os, lvaddr_t addr)
{
    return os;
}


/*
 * -------------------------------------------------------------------------------------------------
 * Configuration Space
 * -------------------------------------------------------------------------------------------------
 */

pv::Tx_Result TranslationUnitBase::control_read(pv::ReadTransaction tx)
{
    access_mode_t mode;
    uint64_t      value;

    Logging::debug("TranslationUnit::control_read([%lx..%lx])", tx.getAddress(),
                   tx.getAddressEndIncl());

    // we want only to support aligned accesses to the configuration space
    if (!tx.isAligned()) {
        Logging::info("TranslationUnit::control_read(): unaligned data access.");
        return pv::Tx_Result(pv::Tx_Data::TX_ALIGNMENTABORT);
    }

    if (tx.isNonSecure()) {
        if (tx.isPrivileged()) {
            mode = ACCESS_MODE_NOSEC_READ;
        } else {
            mode = ACCESS_MODE_USER_READ;
        }
    } else {
        mode = ACCESS_MODE_SEC_READ;
    }

    auto iface = this->get_interface();
    bool r     = iface->handle_register_read(tx.getAddress(), tx.getTransactionByteSize(), mode,
                                             &value);
    if (!r) {
        Logging::debug("TranslationUnit::control_write(): read failed.");
        return pv::Tx_Result(pv::Tx_Data::TX_TRANSFAULT);
    }

    switch (tx.getTransactionByteSize()) {
    case 1: {
        return tx.setReturnData8(value);
    }
    case 2: {
        // XXX: work around,as the following statement somehow causes issues...
        // return tx.setReturnData16(value);
        *static_cast<uint16_t *>(tx.referenceDataValue()) = value;
        return pv::Tx_Result(pv::Tx_Data::TX_OK);
    }
    case 4: {
        return tx.setReturnData32(value);
    }
    case 8: {
        return tx.setReturnData64(value);
    }
    default:
        return pv::Tx_Result(pv::Tx_Data::TX_ALIGNMENTABORT);
    }
}


pv::Tx_Result TranslationUnitBase::control_write(pv::WriteTransaction tx)
{
    access_mode_t mode;
    uint64_t      value;

    Logging::debug("TranslationUnitBase::control_write([%lx..%lx])", tx.getAddress(),
                   tx.getAddressEndIncl());

    // we want only to support aligned accesses to the configuration space
    if (!tx.isAligned()) {
        Logging::debug("TranslationUnitBase::control_write(): unaligned data access.");
        return pv::Tx_Result(pv::Tx_Data::TX_ALIGNMENTABORT);
    }

    if (tx.isNonSecure()) {
        if (tx.isPrivileged()) {
            mode = ACCESS_MODE_NOSEC_READ;
        } else {
            mode = ACCESS_MODE_USER_READ;
        }
    } else {
        mode = ACCESS_MODE_SEC_READ;
    }

    switch (tx.getTransactionByteSize()) {
    case 1:
        value = tx.getData8();
        break;
    case 2:
        value = tx.getData16();
        break;
    case 4:
        value = tx.getData32();
        break;
    case 8:
        value = tx.getData64();
        break;
    default:
        Logging::info("TranslationUnitBase::control_write(): unsupported transaction size.");
        return pv::Tx_Result(pv::Tx_Data::TX_ALIGNMENTABORT);
    }

    auto iface = this->get_interface();
    bool r     = iface->handle_register_write(tx.getAddress(), tx.getTransactionByteSize(), mode,
                                              value);
    if (!r) {
        Logging::debug("TranslationUnitBase::control_write(): write failed.");
        return pv::Tx_Result(pv::Tx_Data::TX_TRANSFAULT);
    }

    return pv::Tx_Result(pv::Tx_Data::TX_OK);
}

pv::Tx_Result TranslationUnitBase::control_debug_read(pv::ReadTransaction tx)
{
    Logging::debug("TranslationUnitBase::control_debug_read([%lx..%lx])", tx.getAddress(),
                   tx.getAddressEndIncl());
    return this->control_read(tx);
}


pv::Tx_Result TranslationUnitBase::control_debug_write(pv::WriteTransaction tx)
{
    Logging::debug("TranslationUnitBase::control_debug_write([%lx..%lx])", tx.getAddress(),
                   tx.getAddressEndIncl());
    return this->control_write(tx);
}


/*
 * -------------------------------------------------------------------------------------------
 * Translations
 * -------------------------------------------------------------------------------------------
 */

#include "pv/RemapRequest.h"

#define BASE_PAGE_SIZE 4096


/// basic translate functionality. This doesn't change anything in the remap request
/// the specific translation unit needs to override this function to provide the actual
/// remapping/translatino function here.
unsigned TranslationUnitBase::handle_remap(pv::RemapRequest &req, unsigned *unpredictable)
{
    Logging::debug("TranslationUnitBase::handle_remap()");

    lpaddr_t addr = req.getOriginalTransactionAddress();
    size_t   size = 1;  // can we get the size somehow?


    // check the supported ranges
    if (addr < this->_inaddr_range_min || addr + size > this->_inaddr_range_max) {
        Logging::error("TranslationUnitBase::handle_remap - request 0x%lx out of supported range "
                       "0x%lx..0x%lx",
                       addr, this->_inaddr_range_min, this->_inaddr_range_max);
        return 1;
    }

    const pv::TransactionAttributes *attr = req.getTransactionAttributes();

    access_mode_t mode;
    if (attr->isNormalWorld()) {
        if (attr->isPrivileged()) {
            if (req.isRead()) {
                mode = ACCESS_MODE_NOSEC_READ;
            } else {
                mode = ACCESS_MODE_NOSEC_WRITE;
            }
        } else {
            if (req.isRead()) {
                mode = ACCESS_MODE_USER_READ;
            } else {
                mode = ACCESS_MODE_USER_WRITE;
            }
        }
    } else {
        if (req.isRead()) {
            mode = ACCESS_MODE_SEC_READ;
        } else {
            mode = ACCESS_MODE_SEC_WRITE;
        }
    }

    // set the translation to be valid only once, to get retriggered
    req.setOnceOnly();

    if (!this->check_permissions(addr, mode)) {
        Logging::info("TranslationUnitBase::handle_remap() - permission failure");
        return 1;
    }

    lpaddr_t dst;
    if (!this->translate(addr, &dst)) {
        Logging::info("TranslationUnitBase::handle_remap() - translation failed");
        return 1;
    }

    Logging::debug("TranslationUnitBase::handle_remap() - translated 0x%lx -> 0x%lx", addr, dst);

    // set the remap base
    req.setRemapPageBase(dst & ~(BASE_PAGE_SIZE - 1));

    return 0;
}

DVM::error_response_t TranslationUnitBase::handle_dvm_msg(DVM::Message *msg, bool ptw)
{
    return DVM::error_response_t(DVM::error_response_t::ok);
}


/*
 * -------------------------------------------------------------------------------------------
 * Translation table walk
 * -------------------------------------------------------------------------------------------
 */


bool TranslationUnitBase::read_paddr(lpaddr_t paddr, uint8_t width, uint64_t *data)
{
    pv::AccessWidth access_width;

    Logging::debug("TranslationUnitBase::translation_table_walk(0x%lx, %u)", paddr, width);
    if (this->_ttw_pvbus == nullptr) {
        Logging::error("TranslationUnitBase::translation_table_walk - no page walker set!");
        return false;
    }

    if (width == 64) {
        access_width = pv::ACCESS_64_BITS;
    } else if (width == 32) {
        access_width = pv::ACCESS_32_BITS;
    } else {
        return false;
    }

    // setup the buffer descriptor
    pv::RandomContextTransactionGenerator::buffer_t bt
        = pv::RandomContextTransactionGenerator::buffer_t(access_width, data, 1);

    // setup the transaction attributes
    pv::TransactionAttributes ta = pv::TransactionAttributes();
    ta.setPTW(true);

    // a new ACE request
    pv::ACERequest req = pv::ACERequest();

    // do the translation
    pv::Tx_Result res = this->_ttw_pvbus->read(&ta, &req, (pv::bus_addr_t)paddr, &bt);

    // return success
    return res.isOK();
}

// A bit of a hack. We need read_paddr to do this.
// State should be declared in the same place as the unit.

void TranslationUnitBase::populate_state() {
    StateBase *state = this->get_state();
    uint64_t temp;

    for (auto it = state->fields.begin(); it != state->fields.end(); it++) {
        auto f = it->second;
        read_paddr(this->base + f->offset, f->bitwidth, &temp);
        f->set_value(temp);
    }
}
