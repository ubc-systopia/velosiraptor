/**
 * The Register Base Class of the Translation Unit
 *
 * SPDX-License-Identifier: MIT
 *
 * Copyright (C) 2022, Reto Achermann (The University of British Columbia)
 */

#ifndef _REGISTER_BASE_H_
#define _REGISTER_BASE_H_ 1


#include <string>

#include "types.hpp"
#include "accessmode.hpp"
#include "state_base.hpp"

/**
 * @brief The RegisterBase class representing a configuration space register
 */
class RegisterBase {
public:
    /**
     * @brief Constructor creating a new register object
     *
     * @param[in] name         name of the register for tracing purposes
     * @param[in] addr         address of the register in the configuration space
     * @param[in] width        width of the register in bytes
     * @param[in] perms        access permissions of the register
     * @param[in] reset_value  value of the register when reset
     * @param[in] state        pointer to the state object of the translation unit
     */
    RegisterBase(std::string name, lpaddr_t addr, uint8_t width,
                 access_perms_t perms = ACCESS_PERMISSION_ALL, uint64_t reset_value = 0,
                 StateBase *state = nullptr);

    /**
     * @brief Constructor creating a new register object
     *
     * @param[in] name         name of the register for tracing purposes
     * @param[in] idx          index if there are multiple copies of the register
     * @param[in] addr         address of the register in the configuration space
     * @param[in] width        width of the register in bytes
     * @param[in] perms        access permissions of the register
     * @param[in] reset_value  value of the register when reset
     * @param[in] state        pointer to the state object of the translation unit
     */
    RegisterBase(std::string name, size_t idx, lpaddr_t addr, uint8_t width,
                 access_perms_t perms = ACCESS_PERMISSION_ALL, uint64_t reset_value = 0,
                 StateBase *state = nullptr);

    /**
     * @brief Destructor. Free's up the res
     */

    ~RegisterBase(void);

    /**
     * @brief Prints the register state
     */
    void print_register(void);


    /**
     * @brief Resets the value of the register to its default value
     *
     * @return the value of the register
     *
     * @note This does only reset the current value of the register, but does not
     *       perform any actions on the state.
     */
    void reset(void)
    {
        this->_value = this->_reset_value;
    }


    /**
     * @brief Performs a read operation triggering the tread actions of the register
     *
     * @param[in]  mode  access mode of the write operation
     * @param[out] data  where to store the read data
     *
     * @return true if the read was successfull, fals if there was a permissions problem
     */
    bool read(access_mode_t mode, uint64_t *data);


    /**
     * @brief Performs a write operation triggering the write actions of the register
     *
     * @param[in] mode  access mode of the write operation
     * @param[in] data  the data to be written
     *
     * @return true if the write was successfull, fals if there was a permissions problem
     */
    bool write(access_mode_t mode, uint64_t data);

    /**
     * @brief Checks whether the register supports the access mode
     *
     * @param[in] mode  access mode to be checked
     *
     * @returns true if the access is permissible.
     */
    bool check_access_mode(access_mode_t mode)
    {
        return (this->_perms & mode);
    }

    /**
     * @brief makes a name that follows the index principle
     */
    static std::string mk_idx_name(std::string name, size_t idx);


    /*
     * -------------------------------------------------------------------------------------------
     * Accessors
     * -------------------------------------------------------------------------------------------
     */


    /**
     * @brief Returns the address of the register
     *
     * @return 64-bit value representing the offset into the configuration space
     */
    uint64_t get_addr(void)
    {
        return this->_addr;
    }

    /**
     * @brief Returns the address of the register
     *
     * @return 64-bit value representing the offset into the configuration space
     */
    const std::string &get_name(void)
    {
        return this->_name;
    }

    /**
     * @brief Returns the mask uf supported values
     *
     * @return 64-bit value representing the mask of supported values
     */
    uint64_t get_value_mask(void)
    {
        return this->_value_mask;
    }

    uint8_t get_width(void)
    {
        return this->_width;
    }


    StateBase *get_state(void)
    {
        return this->_state;
    }

    size_t get_idx(void)
    {
        return this->_idx;
    }

private:
    /**
     * @brief Performs the read operation (assumes permissions are checked)
     *
     * @return the value of the register
     */
    virtual uint64_t do_read(void) = 0;


    /**
     * @brief Performs the write operation (assumes permissions are checked)
     *
     * @param[in] data  the data to be written
     */
    virtual void do_write(uint64_t data) = 0;


    ///< the current value of the register
    uint64_t _value;

    ///< the name of the register
    std::string _name;

    ///< the index into the reg array if multiple of the same
    size_t _idx;

    ///< the address of the register in the configuration space
    lpaddr_t _addr;

    ///< the value mask of the register
    uint64_t _value_mask;

    ///< the value of the register when reset
    uint64_t _reset_value;

    ///< the width of the register in bytes, must be one in 1,2,4, or 8
    uint8_t _width;

    ///< access permissions
    uint8_t _perms;

    ///< reference to the state object of the translation unit
    StateBase *_state;
};

#endif /* _REGISTER_BASE_H_ */
