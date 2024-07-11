/**
 * Represents the field of a translation unit state
 *
 * SPDX-License-Identifier: MIT
 *
 * Copyright (C) 2022, Reto Achermann (The University of British Columbia)
 */

#ifndef _STATE_FIELD_BASE_H_
#define _STATE_FIELD_BASE_H_ 1

#include "fm_util.hpp"
#include <map>
#include <string>

/**
 * @brief Represents a state field
 */
class StateFieldBase {
public:
    /*
     * -------------------------------------------------------------------------------------------
     * Constructors
     * -------------------------------------------------------------------------------------------
     */

    /**
     * @brief constructs a default state field
     */
    StateFieldBase(std::string name, uint64_t offset, lpaddr_t base, uint8_t nbits, uint64_t init_val);

    /**
     * @brief performs a reset on the field
     */
    void reset(void)
    {
        this->value = this->reset_value;
    }

    /*
     * -------------------------------------------------------------------------------------------
     * Debugging
     * -------------------------------------------------------------------------------------------
     */

    /**
     * @brief prints the field
     */
    void print_field(void);

    /*
     * -------------------------------------------------------------------------------------------
     * Accessors
     * -------------------------------------------------------------------------------------------
     */

    /**
     * @brief returns the name of the field
     *
     * @returns a string representing the name of the field
     */
    const std::string& get_name(void) const
    {
        return this->name;
    }

    /**
     * @brief sets the value of the field
     *
     * @param[in] value  new value of the field
     *
     */
    void set_value(uint64_t value)
    {
        this->value = value & this->mask;
    }

    /**
     * @brief obtains the current value in the state field
     *
     * @return the value of the field
     */
    uint64_t get_value(void)
    {
        return this->value;
    }

    /**
     * @brief pushes the value to the backing memory, or pulls the value from the backing memory
     */
    virtual void push_value(void) = 0;
    virtual void pull_value(void) = 0;

    /*
     * -------------------------------------------------------------------------------------------
     * Slices
     * -------------------------------------------------------------------------------------------
     */

    /**
     * @brief obtains the current value in the state field
     *
     * @param[in] name   name of the field
     *
     * @return the value of the slice
     */
    uint64_t get_slice_value(const std::string& name);

    /**
     * @brief updates the value of the field slice
     *
     * @param[in] name   name of the field
     * @param[] value    new value of the field
     *
     * @returns true if the field value has been updated successfully
     */
    bool set_slice_value(const std::string& name, uint64_t value);

    /**
     * @brief adds a new field slice
     *
     * @param[in] name   name of the slice
     * @param[in] start  start bit of the slices (first bit = 0)
     * @param[in] end    end bit of the slice (inclusive)
     */
    bool add_slice(const std::string& name, uint8_t start, uint8_t end);

    ///< the name of the field
    std::string name;

    ///< base of the parent state
    lpaddr_t base;

    ///< offset relative to the base address of the state
    uint64_t offset;

    ///< represents the current value of the field
    uint64_t value;

    ///< represents the reset value of the field
    uint64_t reset_value;

    ///< represents the width of the field in bits
    uint8_t bitwidth;

    ///< the mask for this filed
    uint64_t mask;

private:
    ///< represents the slice map: slice name -> [start, end]
    std::map<std::string, std::pair<uint8_t, uint8_t>> _slices;
};

class RegisterStateFieldBase : public StateFieldBase {
public:
    /**
     * @brief constructs a register state field
     */
    RegisterStateFieldBase(std::string name, uint64_t offset, lpaddr_t base, uint8_t nbits, uint64_t init_val)
        : StateFieldBase(name, offset, base, nbits, init_val)
    {
    }

    /**
     * @brief refreshes the value from the underlying memory. this is a no-op
     */
    void push_value(void) {};
    void pull_value(void) {};
};

class MemoryStateFieldBase : public StateFieldBase {
public:
    /**
     * @brief constructs a register state field
     */
    MemoryStateFieldBase(std::string name, uint64_t offset, lpaddr_t base, uint8_t nbits, uint64_t init_val, pv::RandomContextTransactionGenerator* ptw_pvbus)
        : StateFieldBase(name, offset, base, nbits, init_val)
        , _ptw_pvbus(ptw_pvbus)
    {
    }

    /**
     * @brief refreshes the value from the underlying memory. this is a no-op
     */
    void push_value(void) override;
    void pull_value(void) override;

private:
    ///< access to simulated memory
    pv::RandomContextTransactionGenerator* _ptw_pvbus;
};

#endif /* _STATE_FIELD_BASE_H_ */
