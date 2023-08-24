/**
 * The Register Base Class of the Translation Unit
 *
 * SPDX-License-Identifier: MIT
 *
 * Copyright (C) 2022, Reto Achermann (The University of British Columbia)
 */

#include <assert.h>

#include "logging.hpp"
#include "types.hpp"
#include "state_base.hpp"


StateBase::StateBase()
{
    this->fields = std::map<std::string, StateFieldBase *>();
}


StateBase::StateBase(std::vector<StateFieldBase *> fields)
{
    this->fields = std::map<std::string, StateFieldBase *>();
    for (auto it = fields.begin(); it != fields.end(); it++) {
        bool r = this->add_field(*it);
        if (!r) {
            Logging::error("StateBase::StateBase: failed to insert field %s\n", (*it)->get_name());
        }
    }
}


void StateBase::reset(void)
{
    Logging::info("resetting the state..");
    for (auto it = this->fields.begin(); it != this->fields.end(); it++) {
        it->second->reset();
    }
    Logging::info("state reset completed");
}


void StateBase::print_state_fields(void)
{
    Logging::info("State Fields:");
    Logging::info("      Name         width      currentvalue     (reset value)");
    Logging::info("---------------------------------------------------------------");
    for (auto it = this->fields.begin(); it != this->fields.end(); it++) {
        it->second->print_field();
    }
    Logging::info("---------------------------------------------------------------");
}


bool StateBase::add_field(StateFieldBase *field)
{
    Logging::debug("StateBase::add_field(%s)", field->get_name().c_str());
    auto ret = this->fields.insert(
        std::pair<std::string, StateFieldBase *>(field->get_name(), field));
    return ret.second;
}


StateFieldBase *StateBase::lookup_field_by_name(const std::string &name)
{
    if (this->fields.contains(name)) {
        return this->fields.at(name);
    }
    Logging::error("StateBase::lookup_field: field %s not found\n", name);
    return nullptr;
}


bool StateBase::get_field_value(const std::string &name, uint64_t *value)
{
    if (this->fields.contains(name)) {
        auto field = this->fields.at(name);
        *value     = field->get_value();
        return true;
    }
    Logging::error("StateBase::get_field_value: field %s does not exist\n", name);
    return false;
}


bool StateBase::set_field_value(const std::string &name, uint64_t value)
{
    if (this->fields.contains(name)) {
        auto field = this->fields.at(name);
        field->set_value(value);
        return true;
    }
    Logging::error("StateBase::set_field_value: field %s does not exist\n", name);
    return false;
}

