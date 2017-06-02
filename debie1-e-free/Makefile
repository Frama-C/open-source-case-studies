# frama-c-path.mk contains variables which are specific to each
# user and should not be versioned, such as the path to the
# frama-c binaries (e.g. FRAMAC and FRAMAC_GUI).
# It is an optional include, unnecessary if frama-c is in the PATH.
-include frama-c-path.mk

include ../fcscripts/frama-c.mk

# Define global parameters
CPPFLAGS  = -I code/harness -I code -I code/intel/linux \
            -DTRACE_HARNESS -DTRACE_TARGET
FCFLAGS  +=
EVAFLAGS += -eva-equality-domain

# Export environment variable for Frama-C
export FRAMA_C_MEMORY_FOOTPRINT	= 8

TARGETS=debie1
all: $(TARGETS:%=%.eva)
help:
	@echo "targets: $(TARGETS)"
loop: $(TARGETS:%=%.parse.loop) $(TARGETS:%=%.eva.loop)

debie1.parse: $(sort $(wildcard code/*.c)) code/harness/harness.c \
              code/intel/linux/target.c
debie1.eva: EVAFLAGS += $(shell cat debie1.manually-modified.loop | tr '\\' ' ')
