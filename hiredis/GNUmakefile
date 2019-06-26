# frama-c-path.mk contains variables which are specific to each
# user and should not be versioned, such as the path to the
# frama-c binaries (e.g. FRAMAC and FRAMAC_GUI).
# It is an optional include, unnecessary if frama-c is in the PATH.
-include frama-c-path.mk

FRAMAC_CONFIG ?= frama-c-config
FRAMAC_SHARE = $(shell $(FRAMAC_CONFIG) -print-share-path)
include $(FRAMAC_SHARE)/analysis-scripts/frama-c.mk

# Define global parameters
CPPFLAGS     = -include__fc_builtin.h \
  -D_POSIX_C_SOURCE=200809L
FCFLAGS     += \
  -main eva_main \

EVAFLAGS    += \
  -eva-ilevel 16 \

# Export environment variable for Frama-C
export FRAMA_C_MEMORY_FOOTPRINT	= 8

MAIN_TARGET := hiredis-format
TARGETS = \
$(MAIN_TARGET).eva \
hiredis-misc.eva \

# some targets are disabled from automatic testing until further tuning
#hiredis-tcp \
#hiredis-unix \
#hiredis-tcp-long \
#hiredis-unix-long

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

TEST_SRCS:=$(sort $(wildcard *.c)) $(FRAMAC_SHARE)/libc/string.c \
  $(FRAMAC_SHARE)/libc/netdb.c

hiredis-format.parse: CPPFLAGS += -DEVA_TEST_FORMAT
hiredis-format.parse: $(TEST_SRCS)

hiredis-misc.parse: CPPFLAGS += -DEVA_TEST_MISC
hiredis-misc.parse: $(TEST_SRCS)

hiredis-tcp.parse: CPPFLAGS += -DEVA_TEST_TCP
hiredis-tcp.parse: $(TEST_SRCS)

hiredis-unix.parse: CPPFLAGS += -DEVA_TEST_UNIX
hiredis-unix.parse: $(TEST_SRCS)

hiredis-tcp-long.parse: \
  CPPFLAGS += -DEVA_TEST_TCP -DEVA_TEST_BLOCKING_LONG
hiredis-tcp-long.parse: $(TEST_SRCS)

hiredis-unix-long.parse: \
  CPPFLAGS += -DEVA_TEST_UNIX -DEVA_TEST_BLOCKING_LONG
hiredis-unix-long.parse: $(TEST_SRCS)
