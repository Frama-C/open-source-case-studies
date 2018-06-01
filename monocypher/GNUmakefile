# frama-c-path.mk contains variables which are specific to each
# user and should not be versioned, such as the path to the
# frama-c binaries (e.g. FRAMAC and FRAMAC_GUI).
# It is an optional include, unnecessary if frama-c is in the PATH.
-include frama-c-path.mk

FRAMAC_CONFIG ?= frama-c-config
include $(shell $(FRAMAC_CONFIG) -print-share-path)/analysis-scripts/frama-c.mk

# Define global parameters
CPPFLAGS         +=
FCFLAGS          +=
EVAFLAGS         += -plevel 256

# Export environment variable for Frama-C
export FRAMA_C_MEMORY_FOOTPRINT = 8

TARGETS=monocypher
all: $(TARGETS:%=%.eva)
help:
	@echo "targets: $(TARGETS)"
loop: $(TARGETS:%=%.parse.loop) $(TARGETS:%=%.eva.loop)
parse: $(TARGETS:%=%.parse)
stats: $(TARGETS:%=%.parse) $(TARGETS:%=%.eva)
	../show_stats.sh "$(notdir $(CURDIR))" $^

monocypher.parse: monocypher.c sha512.c test.c

monocypher.eva: EVAFLAGS+=$(shell cat monocypher.slevel | tr -d '\n\\')