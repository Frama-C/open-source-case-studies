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
FCFLAGS     += -machdep gcc_x86_64
EVAFLAGS    += -slevel 10 -eva-equality-domain -val-split-return full
VALBUILTINS +=

# Export environment variable for Frama-C
export FRAMA_C_MEMORY_FOOTPRINT = 8

TARGETS=libmodbus-random-test-client libmodbus-unit-test-server
all: $(TARGETS:%=%.eva)
help:
	@echo "targets: $(TARGETS)"
loop: $(TARGETS:%=%.parse.loop) $(TARGETS:%=%.eva.loop)
parse: $(TARGETS:%=%.parse)
stats: $(TARGETS:%=%.parse) $(TARGETS:%=%.eva)
	../show_stats.sh "$(notdir $(CURDIR))" $^

libmodbus-random-test-client.parse: $(sort $(wildcard src/*.c)) \
  tests/random-test-client.c

libmodbus-unit-test-server.parse: $(sort $(wildcard src/*.c)) \
  tests/unit-test-server.c $(FRAMAC_SHARE)/libc/netdb.c

libmodbus-random-test-client.eva: \
  EVAFLAGS += $(shell cat libmodbus-random-test-client.slevel | tr '\\' ' ')
