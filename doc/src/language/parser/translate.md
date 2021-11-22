# The Translate Method

The translate method is a special method that defines how a unit translates
incoming addresses.

## Definition

The `translate` function defines the translation semantics of a unit depending
on its state.

Mathematically, this is a partial function taking a state, address, and some flags,
to produce a new address.

```
translate :: State -> Addr -> Flags -> Addr option
```

The state is implicit in the specification language (i.e., it can be accessed with
the `state` symbol). The signature of the `translate` method is as follows:

```vrs
fn translate(va: addr, flags: int) -> addr
```

The preconditions should define the conditions under which the translation function
is well-defined and produces a result. Thus, for all inputs satisfying the inputs,
the function is guaranteed to produce an address, otherwise translation fails.

## Example

In this example, `translate` requires that the supplied input address is within the
defined range from `[0, size)` and that the present bit must be set. It then returns
a new address by adding the base to the input address.

```vrs
fn translate(va: addr, flags: int) -> addr
    requires va < state.sz.bytes;
    requires state.flags.present == 1;
{
    return va + state.address.base;
}
```

## Synthesis

The `translate` method is the "verifier" in the synthesis process. For each program
(i.e., implementation of the map/unmap/protect functions) the synthesis algorithm
checks whether `translate` produces the expected result.
For example, that forall addresses with the range `[va, va + i)` translate produces
the right output address.
```
 forall i | 0 <= i < size :: translate(va + i, flags) == pa + i;
```

## Flags

The flags define the permissions, modes, etc. for this translation.  This may include,
read/write/execute permissions, user/supervisor separation, memory protection keys, ...

**TODO:** finalize the notion of flags

## Pre-Conditions

The pre-conditions state the conditions under which the translation is well-defined.
There are three areas to consider when formulating the pre-conditions.

**Input Address (va)**
 - what range of input addresses is valid
 - does this depend on some state field?

**Flags**
 - which kind of access flags do match the permissions set in the translation?
 - Exact match, or what set of flags is still sufficient?

**State**
 - Are there any predicates over the state that must be satisified?



## Static Map Units

The translation function of a static map unit is defined by the `map` definition,
and does not need to be specified.
