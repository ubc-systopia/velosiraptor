/**
 * The Access Modes and Permissions
 *
 * SPDX-License-Identifier: MIT
 *
 * Copyright (C) 2022, Reto Achermann (The University of British Columbia)
 */

#ifndef _ACCESS_MODE_H_
#define _ACCESS_MODE_H_ 1


// access permissions
#define ACCESS_PERMISSION_USER_READ   (1 << 0)
#define ACCESS_PERMISSION_USER_WRITE  (1 << 1)
#define ACCESS_PERMISSION_NOSEC_READ  (1 << 2)
#define ACCESS_PERMISSION_NOSEC_WRITE (1 << 3)
#define ACCESS_PERMISSION_SEC_READ    (1 << 4)
#define ACCESS_PERMISSION_SEC_WRITE   (1 << 5)
#define ACCESS_PERMISSION_ALL         ((1 << 6) - 1)
#define ACCESS_PERMISSION_MASK        ACCESS_PERMISSION_ALL

///< the type of register permissions
typedef unsigned int access_perms_t;


///< defines various register access modes
enum access_mode {
    ACCESS_MODE_USER_READ   = ACCESS_PERMISSION_USER_READ,
    ACCESS_MODE_USER_WRITE  = ACCESS_PERMISSION_USER_WRITE,
    ACCESS_MODE_NOSEC_READ  = ACCESS_PERMISSION_NOSEC_READ,
    ACCESS_MODE_NOSEC_WRITE = ACCESS_PERMISSION_NOSEC_WRITE,
    ACCESS_MODE_SEC_READ    = ACCESS_PERMISSION_SEC_READ,
    ACCESS_MODE_SEC_WRITE   = ACCESS_PERMISSION_SEC_WRITE,
};

///< the type for register access modes
typedef enum access_mode access_mode_t;

#endif /* _ACCESS_MODE_H_ */