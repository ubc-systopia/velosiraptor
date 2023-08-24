/**
 * Translation Unit Base Class
 *
 * SPDX-License-Identifier: MIT
 *
 * Copyright (C) 2022, Reto Achermann (The University of British Columbia)
 */

#ifndef _TRANSLATION_UNIT_BASE_H_
#define _TRANSLATION_UNIT_BASE_H_ 1

#include <stdint.h>
#include <iosfwd>


// FastModels include
#include "pv/DVM.h"
#include "pv/PVBusAddr.h"
#include "pv/PVTransaction.h"  // for pv::Tx_Result

// the types include
#include "types.hpp"
#include "interface_base.hpp"
#include "state_base.hpp"

// forward declaration
namespace sg {
class ComponentTrace;
class ComponentBase;
class CADIBase;
}

namespace pv {
class RandomContextTransactionGenerator;
class TransactionAttributes;
class RemapRequest;
}

#define DEFAULT_RANGE_MIN 0x0
#define DEFAULT_RANGE_MAX ((1UL << 48) - 1)

/**
 * A base class for Translation Units
 */
class TranslationUnitBase {
public:
    /**
     * constructor of the translation unit
     */
    TranslationUnitBase(lpaddr_t                              base,
                        std::string const                     &name,
                        pv::RandomContextTransactionGenerator *ptw_pvbus = nullptr,
                        lvaddr_t                               range_min = DEFAULT_RANGE_MIN,
                        lvaddr_t                               range_max = DEFAULT_RANGE_MAX)
        : base(base)
        , _name(name)
        , _inaddr_range_min(range_min)
        , _inaddr_range_max(range_max)
        , _ttw_pvbus(ptw_pvbus)
    {
    }


    /*
     * -------------------------------------------------------------------------------------------
     * Printing Functionality
     * -------------------------------------------------------------------------------------------
     */

    // prints the global state
    virtual std::ostream &print_global_state(std::ostream &os);

    // prints the translation steps for an address
    virtual std::ostream &print_translation(std::ostream &os, lvaddr_t addr);


    /*
     * -------------------------------------------------------------------------------------------
     * Reset
     * -------------------------------------------------------------------------------------------
     */

    /**
     * resets the simulation of the components
     */
    virtual void reset(void);


    /**
     * @brief asserts the reset signal
     *
     * @param[in]   signal_level the signal level to be asserted
     */
    virtual void set_reset(bool signal_level);


    /*
     * -------------------------------------------------------------------------------------------
     * Accessors
     * -------------------------------------------------------------------------------------------
     */


    /**
     * @brief obtains a pointer to the interface
     *
     * @returns pointer ot the interface of the unit
     */
    virtual InterfaceBase *get_interface(void) = 0;

    /**
     * @brief obtains a pointer to the state
     *
     * @returns pointer to the state
     */
    virtual StateBase *get_state(void) = 0;


    /*
     * -------------------------------------------------------------------------------------------
     * Configuration Space Accesssors
     * -------------------------------------------------------------------------------------------
     */


    /**
     * @brief Handles a read transaction for the configuration space register file
     *
     * @param tx     the read transaction information
     */
    virtual pv::Tx_Result control_read(pv::ReadTransaction tx);

    /**
     * Handles a write transaction for the configuration space register file
     *
     * @param tx     the write transaction information
     */
    virtual pv::Tx_Result control_write(pv::WriteTransaction tx);

    /**
     * Handles a debug read transaction for the configuration space register file
     *
     * @param tx     the debug read transaction information
     */
    virtual pv::Tx_Result control_debug_read(pv::ReadTransaction tx);

    /**
     * Handles a debug write transaction for the configuration space register file
     *
     * @param tx     the debug write transaction information
     */
    virtual pv::Tx_Result control_debug_write(pv::WriteTransaction tx);


    /*
     * -------------------------------------------------------------------------------------------
     * Translations
     * -------------------------------------------------------------------------------------------
     */


    /**
     * translates an address via a remap request
     *
     * @param[in]   req            the remap request information, updated in place
     * @param[out]  unpredictable  a pointer to a variable that will be set to true if the translation
     */
    unsigned handle_remap(pv::RemapRequest &req, unsigned *unpredictable);


    /**
     * handles a DVM message from the downstream port
     *
     * @param[in]   msg    the DVM message
     * @param[out]  ptw    whether the message was received on the page walker port
     */
    virtual DVM::error_response_t handle_dvm_msg(DVM::Message *msg, bool ptw);


    /*
     * -------------------------------------------------------------------------------------------
     * Translations
     * -------------------------------------------------------------------------------------------
     */


    /**
     * @brief reads from physical memory
     *
     * @param[in]  addr   the address to read from
     * @param[in]  width  the amount of bits to read
     * @param[out] data   returns the read data
     */
    bool read_paddr(lpaddr_t addr, uint8_t width, uint64_t *data);

    /**
     * @brief Fills the state given a base address
     *
     * @param[in]  base   the address to read from
     */
    void populate_state();

    ///< base address
    lpaddr_t base;

  private:

    /**
     * @param[in] src_addr   the virtual address to be translated
     * @param[in] size       the size of the translation request
     * @param[in] mode       access mode of the request
     * @param[out] dst_addr  the translated address
     *
     * @returns true if the translation was successful, false otherwise
     */
    virtual bool translate(lvaddr_t src_addr, lpaddr_t *dst_addr)
        = 0;

    std::string _name;

    ///< the minimum address supported by this translation unit
    lvaddr_t _inaddr_range_min;

    ///< the maximum address (including) supported by this translation unit
    lvaddr_t _inaddr_range_max;

    ///< the page table walker
    pv::RandomContextTransactionGenerator *_ttw_pvbus;
};

#endif /* _TRANSLATION_UNIT_BASE_H_ */
