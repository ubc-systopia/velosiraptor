# Arm FastModels Translation Unit Components
#
# SPDX-License-Identifier: MIT
#
# Copyright (C) 2022, Reto Achermann (The University of British Columbia)

# This file is auto-generated

# Set the build directory
BUILD_DIR := $(CURDIR)/build
SOURCE_DIR := $(CURDIR)/src
FRAMEWORK_DIR := $(CURDIR)/../framework/build

# compiler flags
CC      := g++
CCFLAGS := -Wall -O3 -Werror -std=c++2a -fPIC
CCFLAGS += -I $(SOURCE_DIR)/include
CCFLAGS += -I $(FRAMEWORK_DIR)/include
CCFLAGS += -I $(PVLIB_HOME)/include
CCFLAGS += -I $(PVLIB_HOME)/include/fmruntime
CCFLAGS += -MMD -MP

# archive flags
AR      := ar
ARFLAGS := rcs

# linker flags
LD      := g++
LDFLAGS := -pthread

# creating directories
MKDIR := mkdir -p

# the simgen tool
SIMGEN := simgen

# Source Files
TRANSLATION_UNIT_SRCS := $(SOURCE_DIR)/unit.cpp
TRANSLATION_UNIT_SRCS += $(SOURCE_DIR)/interface.cpp
TRANSLATION_UNIT_SRCS += $(SOURCE_DIR)/state.cpp
TRANSLATION_UNIT_SRCS += $(SOURCE_DIR)/registers.cpp

# Object Files
TRANSLATION_UNIT_OBJS := $(TRANSLATION_UNIT_SRCS:$(SOURCE_DIR)/%.cpp=$(BUILD_DIR)/objs/%.o)

# The Translation Unit Library
TRANSLATION_UNIT_LIB  := $(BUILD_DIR)/lib/libunit.a

# building the library
$(TRANSLATION_UNIT_LIB): $(TRANSLATION_UNIT_OBJS)
	$(MKDIR) $(@D)
	$(AR) $(ARFLAGS) -o $@ $^

PLATFORM_BIN  := $(BUILD_DIR)/plat_example_sim
PLATFORM_PROJ := platform/ExamplePlatform.sgproj
PLATFORM_LISA := platform/ExamplePlatform.lisa

$(PLATFORM_BIN): $(TRANSLATION_UNIT_LIB) $(PLATFORM_LISA) $(PLATFORM_PROJ) TranslationUnit.lisa
	$(MKDIR) $(@D)
	BUILD_DIR=$(BUILD_DIR) $(SIMGEN) -v on --num-comps-file 50 --gen-sysgen --warnings-as-errors \
									 -p $(PLATFORM_PROJ) --build-directory $(BUILD_DIR)/plat_example -b
	ln -s -f $(BUILD_DIR)/plat_example/isim_system $@

run: $(PLATFORM_BIN)
	$(PLATFORM_BIN) --data Memory0=bootimg.bin@0x0

# Targets
.DEFAULT_GOAL = all
all: $(TRANSLATION_UNIT_LIB) $(PLATFORM_BIN)
lib: $(TRANSLATION_UNIT_LIB)

# Compilation Rules
$(BUILD_DIR)/objs/%.o: $(SOURCE_DIR)/%.cpp
	$(MKDIR) $(@D)
	$(CC) $(CCFLAGS) -c -o $@ $<

# clean up
clean:
	rm -rf $(BUILD_DIR)
