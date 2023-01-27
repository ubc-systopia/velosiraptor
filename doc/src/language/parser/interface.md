# Interface

The interface of a [unit](units.md) provides the set of operations that
system software can perform to configure the translation hardware. Similarly
to the [state](state.md), the interface consists of a set of fields that
represent the API of the translation unit. System software can only
interact with the translation hardware configuration through its interface.


```
             +-------------+                      +-------------+
 operation   |             |  state transitions   |             |
-----------> |  Interface  | <=================>  |    state    |
             |             |                      |             |
             +-------------+                      +-------------+
```

## Grammar

```
INTERFACE           := NONE_INTERFACE
                     | MMIO_INTERFACE
                     | MEMORY_INTERFACE
                     | REGISTER_INTERFACE

NONE_INTERFACE      := KW_NONE SEMICOLON

MMIO_INTERFACE      := KW_MMIO LPAREN ARGLIST RPAREN INTERFACE_BODY

MEMORY_INTERFACE    := KW_MEMORY LPAREN ARGLIST RPAREN INTERFACE_BODY

REGISTER_INTERFACE  := KW_REGISTER LPAREN ARGLIST RPAREN INTERFACE_BODY

INTERFACE_BODY      := LBRACE [ INTERFACE_FIELD ]+ RBRACE

INTERFACE_FIELD     := IDENT FIELD_PARAMS LBRACE
                       LAYOUT READACTION? WRITEACTION? RBRACE SEMICOLON

LAYOUT              := KW_LAYOUT BITSLICE_BLOCK

READACTION          := KW_READACTION ACTIONS_BLOCK SEMICOLON
WRITEACTION         := KW_READACTION ACTIONS_BLOCK SEMICOLON

ACTIONS_BLOCK       := LBRACE [ ACTION [COMMA ACTION]* ] RBRACE
ACTION              := EXPR [LARROW | RARROW ] EXPR

ARGLIST             := [ ARG [COMMA ARG]* ]?
ARG                 := IDENT COLON TYPE
```

## Example
```vrs
interface = Memory(base : addr) {
    address [base, 0, 8] {
        Layout {
            0  63 base
        };
        ReadActions {
            interface.address <- state.address;
        };
        WriteActions {
            interface.address -> state.address;
        };
    };
    sz [base, 8, 8] {
        Layout {
            0  63 bytes
        };
        ReadActions {
            interface.sz <- state.sz;
        };
        WriteActions {
            interface.sz -> state.sz;
        };
    };
}
```

## Interface Kinds

Currently, the language supports four different interface kinds that define *how* system software needs to invoke the interface.

**None.** There is nothing to be configured by this unit, i.e., the unit is merely
a static map.

**Memory Interface.** This is the interface to an in-memory data structure (e.g., a page
table). Software uses loads/stores to interact with it. This means, the interface is in
fact an identity of the state, and software can effectively access the entire state.

**MMIO Interface.**
These are memory mapped registers. Software uses non-cached load/stores
to interact with this interface. In contrast to the memory interface, parts of the
state may not be directly accessible from the interface.

**Register Interface**
These are registers that do not have a memory address, but rather the CPU uses
loads/stores to an special CPU registers, or even issues a specific instruction to
do so

## Actions

Recall the set of interface fields correspond to the API system software uses to
interact with the translation hardware where each field corresponds to a function.
This API function in turn can be invoked through a read or write operation on the field.

To specify the behavior, the interface specification includes a set of actions that
may modify the state of the translation hardware. This set of actions connect the
state with the interface: The following example expresses a single address field
with the corresponding actions. Writing to the address field copies the content
into the address field of the state. Likewise, reading the address field copies the
current value in the state.

```vrs
interface = Memory(base : addr) {
    address [base, 0, 8] {
        Layout {
            0  63 base
        };
        ReadActions {
            interface.address <- state.address;
        };
        WriteActions {
            interface.address -> state.address;
        };
    };
};
```
**No actions**
The set of actions can be empty. This means that the corresponding interface field
does not have a "direct" connection to the state, i.e., when the interface field
is written or read, nothing happens with regard to the state.

**Multiple Actions**
The blocks can contain multiple actions. For example, setting the base address and
the enabled bit at the same time, or some kind of "commit" semantics where a transition
is prepared in some interface fields, then committed when writing to another field.