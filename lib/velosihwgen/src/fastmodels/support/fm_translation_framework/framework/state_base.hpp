/**
 * Represents the state of a translation unit
 *
 * SPDX-License-Identifier: MIT
 *
 * Copyright (C) 2022, Reto Achermann (The University of British Columbia)
 */

#ifndef _STATE_BASE_H_
#define _STATE_BASE_H_ 1

#include <map>
#include <vector>
#include <string>

#include "state_field_base.hpp"

class StateBase {
public:
    /*
     * -------------------------------------------------------------------------------------------
     * Constructors
     * -------------------------------------------------------------------------------------------
     */

    /**
     * @brief constructs a default, empty state
     */
    StateBase(void);

    /**
     * @brief create a new StateBase class with the given fields
     *
     * @param[in] fields  the fields of the state
     */
    StateBase(std::vector<StateFieldBase *> fields);


    /**
     * @brief prints the fields of the current staste
     */
    void print_state_fields(void);


    /**
     * @brief reset the state to the default values
     */
    void reset(void);


    /*
     * -------------------------------------------------------------------------------------------
     * Field Access
     * -------------------------------------------------------------------------------------------
     */


    /**
     * @brief tries to find the field with the given name
     *
     * @param[in]  name   name of the field
     *
     * @returns returnes pointer to the field object
     */
    StateFieldBase *lookup_field_by_name(const std::string &name);


    /**
     * @brief obtains the current value in the state field
     *
     * @param[in] name    name of the field
     * @param[out] value  pointer to where to store the field value
     *
     * @return true if the field value has been updated successfully
     */
    bool get_field_value(const std::string &name, uint64_t *value);


    /**
     * @brief updates the value of the state field
     *
     * @param[in] name   name of the field
     * @param[in] value  new value of the field
     *
     * @returns true if the field value has been updated successfully
     */
    bool set_field_value(const std::string &name, uint64_t value);

    ///< stores a map between field names and field objects
    std::map<std::string, StateFieldBase *> fields;

protected:
    /**
     * @brief adds a field to the state
     *
     * @param[in] field  the field to be added
     *
     * @returns true if the field was added, false if the field already exists
     */
    bool add_field(StateFieldBase *field);
};

#endif /* _STATE_BASE_H_ */
