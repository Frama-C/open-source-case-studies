# frama-c-path.mk contains variables which are specific to each
# user and should not be versioned, such as the path to the
# frama-c binaries (e.g. FRAMAC and FRAMAC_GUI).
# It is an optional include, unnecessary if frama-c is in the PATH.
-include frama-c-path.mk

FRAMAC_CONFIG ?= frama-c-config
FRAMAC_SHARE=$(shell $(FRAMAC_CONFIG) -print-share-path)
include $(FRAMAC_SHARE)/analysis-scripts/frama-c.mk

# Define global parameters
CPPFLAGS     = -include__fc_libc_fixes.h -I src
FCFLAGS     += \
  -machdep gcc_x86_64 \

EVAFLAGS    += \
  -slevel 23 \
  -eva-equality-domain \
  -eva-split-return full \

# Export environment variable for Frama-C
export FRAMA_C_MEMORY_FOOTPRINT = 8

MAIN_TARGET := libmodbus-random-client
TARGETS = $(MAIN_TARGET).eva libmodbus-unit-server.eva
all: $(TARGETS)
help:
	@echo "targets: $(TARGETS)"
display-targets:
	@echo "$(TARGETS)"

# The following targets are optional and provided for convenience only
parse: $(TARGETS:%.eva=%.parse)
loop: $(TARGETS:%.eva=%.parse.loop) $(TARGETS:%=%.loop)
gui: $(MAIN_TARGET).eva.gui

stats: $(TARGETS:%.eva=%.parse) $(TARGETS)
	../show_stats.sh "$(notdir $(CURDIR))" $^

libmodbus-random-client.parse: $(sort $(wildcard src/*.c)) \
  tests/random-test-client.c $(FRAMAC_SHARE)/libc/string.c

libmodbus-unit-server.parse: $(sort $(wildcard src/*.c)) \
  tests/unit-test-server.c $(FRAMAC_SHARE)/libc/netdb.c \
  $(FRAMAC_SHARE)/libc/string.c
