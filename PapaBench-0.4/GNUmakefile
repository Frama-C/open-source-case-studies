# frama-c-path.mk contains variables which are specific to each
# user and should not be versioned, such as the path to the
# frama-c binaries (e.g. FRAMAC and FRAMAC_GUI).
# It is an optional include, unnecessary if frama-c is in the PATH.
-include frama-c-path.mk

FRAMAC_CONFIG ?= frama-c-config
include $(shell $(FRAMAC_CONFIG) -print-share-path)/analysis-scripts/frama-c.mk

# Define global parameters
CPPFLAGS += -DUBX -D__FAKE_FOR_IA32__ -D_XOPEN_SOURCE=700 \
  -Isw/airborne/fly_by_wire \
  -Isw/var/include \
  -Isw/airborne/autopilot \
  -Iavr/include \
  -iquote sw/include \

FCFLAGS  += -absolute-valid-range 0-0xFF -warn-special-float nan
EVAFLAGS +=

# Export environment variable for Frama-C
export FRAMA_C_MEMORY_FOOTPRINT	= 8

TARGETS=autopilot
all: $(TARGETS:%=%.eva)
help:
	@echo "targets: $(TARGETS)"
loop: $(TARGETS:%=%.parse.loop) $(TARGETS:%=%.eva.loop)
parse: $(TARGETS:%=%.parse)
stats: $(TARGETS:%=%.parse) $(TARGETS:%=%.eva)
	../show_stats.sh "$(notdir $(CURDIR))" $^

autopilot.parse: $(sort $(wildcard sw/airborne/autopilot/*.c)) sw/lib/c/math.c \
  $(shell $(FRAMAC_CONFIG) -print-share-path)/libc/math.c
