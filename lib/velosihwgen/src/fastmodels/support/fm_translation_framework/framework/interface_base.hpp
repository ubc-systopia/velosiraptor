/**
 * The Interface Base Class of the Translation Unit
 *
 * SPDX-License-Identifier: MIT
 *
 * Copyright (C) 2022, Reto Achermann (The University of British Columbia)
 */

#ifndef _INTERFACE_BASE_H_
#define _INTERFACE_BASE_H_ 1

#include <map>

#include "types.hpp"
#include "register_base.hpp"

/**
 * @brief the base class of interfaces
 */
class InterfaceBase {
public:
    /**
     * @brief Constructor creating a new interface object
     *
     * @param[in] state  pointer to the state object of the translation unit
     */
    InterfaceBase(StateBase *state);


    /**
     * @brief prints the interface state
     */
    void debug_print_interface(void);


    /**
     * @brief reset the interface registers to predefined values
     */
    void reset(void);


    /**
     * @brief returns the register with a given name
     *
     * @returns pointer to the register object with the given name
     */
    RegisterBase *lookup_register_by_name(const std::string &name);


    /**
     * @brief returns the register with a given address
     *
     * @returns pointer to the register object at the given address
     *
     * Note: the register must have a precise name
     */
    RegisterBase *lookup_register_by_address(lpaddr_t addr);


    /**
     * @brief checks whether the given register is valid
     *
     * @param[in] addr  the base address of the register
     *
     * @returns true if the register is valid, false otherwise
     */
    bool is_address_valid(lpaddr_t addr)
    {
        return this->_register_by_addr.find(addr) != this->_register_by_addr.end();
    }


    /**
     * @brief checks whether the given register is valid
     *
     * @param[in] name  the name of the register
     *
     * @returns true if the register is valid, false otherwise
     */
    bool is_name_valid(const std::string &name)
    {
        return this->_register_by_name.find(name) != this->_register_by_name.end();
    }


    /*
     * -------------------------------------------------------------------------------------------
     * Handling of Write Actions
     * -------------------------------------------------------------------------------------------
     */


    /**
     * @brief Handles a write action of `width bytes at `addr`
     *
     * @param[in] addr    the address of the write action
     * @param[in] width   the width of the read action in bytes
     * @param[in] data    the data to be written
     *
     * @returns true if the write action was handled successfully, false otherwise
     */
    bool handle_register_write(lpaddr_t addr, uint8_t width, access_mode_t mode, uint64_t data);


    /**
     * @brief Handles a write action of `width bytes at `addr`
     *
     * @param[in] addr    the address of the write action
     * @param[in] width   the width of the read action in bytes
     *
     * @returns true if the write action was handled successfully, false otherwise
     */
    bool handle_register_write(const std::string &name, uint8_t width, access_mode_t mode,
                               uint64_t data);

    /*
     * -------------------------------------------------------------------------------------------
     * Handling of Read Actions
     * -------------------------------------------------------------------------------------------
     */


    /**
     * @brief Handles a read action of `width` bytes at `addr`
     *
     * @param[in]  addr   the address of the read action
     * @param[in]  width  the width of the read action in bytes
     * @param[out] data   where to store the read data
     *
     * @returns true if the read action was handled successfully, false otherwise
     */
    bool handle_register_read(lpaddr_t addr, uint8_t width, access_mode_t mode, uint64_t *data);


    /**
     * @brief Handles a read action on `name`
     *
     * @param[in]  name   the name of the register
     * @param[out] data   where to store the read data
     *
     * @returns true if the read action was handled successfully, false otherwise
     */
    bool handle_register_read(const std::string &name, uint8_t width, access_mode_t mode,
                              uint64_t *data);


protected:
    /**
     * @brief add a register to the maps
     *
     * @param[in] reg   register to be added
     *
     * @returns true if the register was added successfully, false if there was an overlap
     */
    bool add_register(RegisterBase *reg);

private:
    bool handle_register_read(RegisterBase *reg, uint8_t width, access_mode_t mode, uint64_t *data);
    bool handle_register_write(RegisterBase *reg, uint8_t width, access_mode_t mode, uint64_t data);


    /**
     * @brief the map of names to registers
     */
    std::map<std::string, RegisterBase *> _register_by_name;

    /**
     * @brief a map of addresses to registers
     */
    std::map<lpaddr_t, RegisterBase *> _register_by_addr;

    /**
     * @brief reference to the state
     */
    StateBase *_state;
};

#endif /* _INTERFACE_BASE_H_ */
