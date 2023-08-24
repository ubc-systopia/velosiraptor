/**
 * Logging class implementation
 *
 * SPDX-License-Identifier: MIT
 *
 * Copyright (C) 2022, Reto Achermann (The University of British Columbia)
 */

#include <cstdio>
#include <stdlib.h> /* exit, EXIT_FAILURE */
#include "logging.hpp"

bool     Logging::enabled = false;
LogLevel Logging::level   = LOG_LEVEL_DEFAULT;


/**
 * @brief Initializes the logging facility
 *
 * @param level     the log level to activate
 */
void Logging::init(LogLevel level)
{
    Logging::level   = level;
    Logging::enabled = true;
}

void Logging::enable(void)
{
    Logging::enabled = true;
}

void Logging::disable(void)
{
    Logging::enabled = true;
}

void Logging::set_level(LogLevel level)
{
    Logging::level = level;
}

void Logging::debug(const char *format, ...)
{
    va_list args;

    va_start(args, format);
    Logging::log(LOG_LEVEL_DEBUG, "DEBUG", format, args);
}

void Logging::info(const char *format, ...)
{
    va_list args;

    va_start(args, format);
    Logging::log(LOG_LEVEL_INFO, " INFO", format, args);
}

void Logging::warn(const char *format, ...)
{
    va_list args;

    va_start(args, format);
    Logging::log(LOG_LEVEL_WARNING, " WARN", format, args);
}

void Logging::error(const char *format, ...)
{
    va_list args;

    va_start(args, format);
    Logging::log(LOG_LEVEL_ERROR, "ERROR", format, args);
}

void Logging::panic(const char *format, ...)
{
    va_list args;

    va_start(args, format);
    Logging::enabled = true;
    Logging::log(LOG_LEVEL_ERROR, "ERROR", format, args);
    exit(EXIT_FAILURE);
}

void Logging::log(LogLevel level, const char *prefix, const char *format, va_list args)
{
    if (Logging::enabled && level <= Logging::level) {
        printf("[UNIT] [%s] ", prefix);
        vprintf(format, args);
        printf("\n");
    }
}
