# Introduction

Setting up translation hardware is a security and correctness critical operation.
Any mistake can lead to program crashes, data corruption and loss, or violation of
isolation guarantees. System software (e.g., firmware, bootloaders, hypervisors, or
operating systems) interface with translation hardware to set up the right translations
adhering to the security and isolation policies in the system.

Up to now, system software developers needed to implement the drivers to interface with
the translation hardware for every new platform and for every piece of system software.
This means that work not only had to be duplicated over and over again, but also potential
errors would be replicated as well.

In contrast, VelosiRaptor uses a single specification of translation hardware that is
expressed in an intuitive domain specific language to describe the behavior of translation
hardware. From this specification we can generate both, the system software code that
interfaces with the translation hardware, and the translation hardware itself.

This removes the burden to write translation hardware driver code from system software
developers: new architectures and translation hardware is supported by simply writing
a spec and then having the relevant systems code generated. VelosiRaptor uses software
synthesis to support generation of higher-level functions like map/unmap/protect.

Lastly, VelosiRaptor enables research in translation hardware itself by specifying
a tailored translation scheme for a specific use case (e.g., FPGAs, accelerators, ...).
VelosiRaptor can not only generate the system software components to interface with
the translation hardware, but also produce the corresponding hardware descriptions
(eventually / future work).


## This Document

This document describes the architecture of the VelosiRaptor toolchain, its command line
interface, the specification language, and its synthesis/code generation functionality.
