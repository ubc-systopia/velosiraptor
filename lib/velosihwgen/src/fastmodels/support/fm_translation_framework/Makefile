# Arm FastModels Translation Unit Framework Support Library
#
# SPDX-License-Identifier: MIT
#
# Copyright (C) 2022, Reto Achermann (The University of British Columbia)

# Set the build directory
BUILD_DIR := $(CURDIR)/build
SOURCE_DIR := $(CURDIR)/framework

# compiler flags
CC      := g++
CCFLAGS := -Wall -O3 -Werror -std=c++2a -fPIC
CCFLAGS += -I include
CCFLAGS += -I $(SOURCE_DIR)/include
CCFLAGS += -I $(PVLIB_HOME)/include
CCFLAGS += -I $(PVLIB_HOME)/include/fmruntime
CCFLAGS += -MMD -MP

# archive flags
AR      := ar
ARFLAGS := rcs

# creating directories
MKDIR := mkdir -p

# Source Files
FRAMEWORK_SRCS := $(SOURCE_DIR)/translation_unit_base.cpp
FRAMEWORK_SRCS += $(SOURCE_DIR)/state_base.cpp
FRAMEWORK_SRCS += $(SOURCE_DIR)/state_field_base.cpp
FRAMEWORK_SRCS += $(SOURCE_DIR)/interface_base.cpp
FRAMEWORK_SRCS += $(SOURCE_DIR)/register_base.cpp
FRAMEWORK_SRCS += $(SOURCE_DIR)/logging.cpp

# Include Files
FRAMEWORK_HDRS := $(SOURCE_DIR)/include/accessmode.hpp
FRAMEWORK_HDRS += $(SOURCE_DIR)/include/logging.hpp
FRAMEWORK_HDRS += $(SOURCE_DIR)/include/state_base.hpp
FRAMEWORK_HDRS += $(SOURCE_DIR)/include/translation_unit_base.hpp
FRAMEWORK_HDRS += $(SOURCE_DIR)/include/interface_base.hpp
FRAMEWORK_HDRS += $(SOURCE_DIR)/include/register_base.hpp
FRAMEWORK_HDRS += $(SOURCE_DIR)/include/state_field_base.hpp
FRAMEWORK_HDRS += $(SOURCE_DIR)/include/types.hpp


# Object Files
FRAMEWORK_OBJS := $(FRAMEWORK_SRCS:$(SOURCE_DIR)/%.cpp=$(BUILD_DIR)/objs/%.o)

# Installed Includes
FRAMEWORK_INCS := $(FRAMEWORK_HDRS:$(SOURCE_DIR)/%.hpp=$(BUILD_DIR)/%.hpp)

# Library
FRAMEWORK_LIB  := $(BUILD_DIR)/lib/libframework.a

# building the library
$(FRAMEWORK_LIB): $(FRAMEWORK_OBJS)
	$(MKDIR) $(@D)
	$(AR) $(ARFLAGS) -o $@ $^

# Dependencies
DEPS := $(shell find $(BUILD_DIR)/ -type f -name '*.d')
-include $(DEPS)

# Targets
.DEFAULT_GOAL = all
all: $(FRAMEWORK_LIB) $(FRAMEWORK_INCS)

# Compilation Rules
$(BUILD_DIR)/objs/%.o: $(SOURCE_DIR)/%.cpp
	$(MKDIR) $(@D)
	$(CC) $(CCFLAGS) -c -o $@ $<

$(BUILD_DIR)/include/%.hpp: $(SOURCE_DIR)/%.hpp
	$(MKDIR) $(@D)
	cp $< $@

# Targets
.DEFAULT_GOAL = all

all: $(FRAMEWORK_LIB)

format:
	find $(SOURCE_DIR) -regex '.*\.\(cpp\|hpp\)' -exec clang-format -style=file -i {} \;

# clean up
clean:
	rm -rf $(BUILD_DIR)
