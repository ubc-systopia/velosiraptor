# Map/Unmap/Protect Functions

The map/unmap/protect functions are higher-level operations that system software uses
to configure the translation units. The implementations of these methods are
*synthesized* by the toolchain.

The purpose of the map/unmap/protect functions is to provide the necessary constraints
to the synthesis algorithm.

All three methods are causing state transitions, and they may or may not be supported by
the underlying hardware.

## Example
The following example provides an illustration: it adds constraints on the provided addresses
and the size parameters.

```vrs
fn map(va: addr, sz: size, flags: int, pa : addr) -> bool
    requires va == 0x0;
    requires pa <= 0xffffffffffff;
    requires pa + sz <= 0xffffffffffff;
    requires sz <= 0xffffffff;
    requires sz >= 16;

    ensures forall i : addr :: 0 <= i && i < sz && translate(va + i, flags) == pa + i;
{} // empty
```

## Map
The `map` installs a new mapping with the given permissions. It ensures that the
supplied address range `[va, va + size)` maps onto the range `[pa, pa + size)`.

This corresponds to the following function:
```
map :: Addr -> Size -> Addr -> Flags -> State -> State
```
The signature in the specification language:
```vrs
fn map(va: addr, sz: size, flags: int, pa : addr) -> bool;
```

In most cases, this will overwrite the already existing mapping.

## Unmap

The `unmap` method removes the existing mapping in the translation unit. It ensures that
the supplied address range `[va, va+size)` is no longer accessible. This is similar
to removing all access rights with `protect`, but it also removes any information
on the previous mapping.

This corresponds to the following function:
```
unmap :: Addr -> Size -> State -> State
```

The signature in the specification language:
```vrs
fn unmap(va: addr, sz: size) -> bool;
```

In most cases, the input address and the size must match the already existing values,
or it shrinks the second part of the mapping.


## Protect
The `protect` method changes the access permissions on an existing mapping. It
ensures that the supplied address range `[va, va+size)` adheres to the new access rights.

This corresponds to the following function:
```
protect :: Addr -> Size -> Flags -> State -> State
```

The signature in the specification language:
```vrs
fn protect(va: addr, sz: size, flags: int) -> bool;
```

In most cases, the input address and the size must match the already existing values
(i.e., there is no further split possible)


## Pre-Conditions

The following some suggestions on the kind of pre-conditions one may write.

**Input Address (VA)**
 - Supported address values (min, max, alignment)?
 - Is it always 0? (a segment is always `[0, size)`
 - Limits w.r.t. `va + size`
 - Same as existing value in the state?

**Size**
 - Supported size values (min, max, alignment)?
 - Same as existing value in the state?

**Flags**
 - what flags are supported?

**Output Address (PA)**
 - Supported size values (min, max, alignment)?
 - Limits w.r.t. `pa + size`
 - Same as existing value in the state?