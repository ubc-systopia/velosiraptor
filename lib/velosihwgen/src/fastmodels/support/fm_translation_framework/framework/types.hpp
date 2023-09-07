/**
 * Type Definitions
 *
 * SPDX-License-Identifier: MIT
 *
 * Copyright (C) 2022, Reto Achermann (The University of British Columbia)
 */

#ifndef _TYPES_H_
#define _TYPES_H_ 1

#include <stdint.h>

/**
 * defines the local virtual address of the translation unit (input)
 */
typedef uint64_t lvaddr_t;

/**
 * defines the local physical addrss of the translation unit (output)
 */
typedef uint64_t lpaddr_t;

/**
 * defines the local physical addrss of the translation unit (output)
 */
typedef uint64_t genaddr_t;


///< stringify a macro
#define STRINGIFY(x) #x

#endif /* _TYPES_H_ */