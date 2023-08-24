/**
 * Logging class
 *
 * SPDX-License-Identifier: MIT
 *
 * Copyright (C) 2022, Reto Achermann (The University of British Columbia)
 */

#ifndef _LOGGING_H_
#define _LOGGING_H_ 1

#include <cstdarg>

// the logging levels
enum LogLevel : char {
    LOG_LEVEL_NONE = 0,
    LOG_LEVEL_ERROR,
    LOG_LEVEL_WARNING,
    LOG_LEVEL_INFO,
    LOG_LEVEL_DEBUG
};

///< the default log level
#define LOG_LEVEL_DEFAULT LOG_LEVEL_ERROR

/**
 * the logging class
 */
class Logging {
public:
    /**
     * Initializes the logging subsystem
     *
     * @param[in] level the log level
     */
    static void init(LogLevel level);

    /**
     * enables the logging output
     */
    static void enable(void);

    /**
     * disables the logging output
     */
    static void disable(void);

    /**
     * sets the log level
     *
     * @param[in] level the log level
     */
    static void set_level(LogLevel level);

    /**
     * generates a new DEBUG log message
     *
     * @param[in] format  the log message
     */
    static void debug(const char *format, ...);

    /**
     * generates a new INFO log message
     *
     * @param[in] format  the log message
     */
    static void info(const char *format, ...);

    /**
     * generates a new WARN log message
     *
     * @param[in] format  the log message
     */
    static void warn(const char *format, ...);

    /**
     * generates a new ERROR log message
     *
     * @param[in] format  the log message
     */
    static void error(const char *format, ...);


    /**
     * generates a new panic log message and terminates the program
     *
     * @param[in] format  the log message
     */
    static void panic(const char *format, ...);

private:
    /**
     * stores the current log level
     */
    static LogLevel level;

    /**
     * flag indicating whether the logging is enabled
     */
    static bool enabled;

    /**
     * the logging function
     *
     * @param[in] level   the log level of this message
     * @param[in] prefix  the prefix of the log message
     * @param[in] fmt     the logging format
     * @param[in] args    the arguments for the format string
     */
    static void log(LogLevel level, const char *prefix, const char *fmt, va_list args);
};

#endif /* _LOGGING_H_ */