# TEMPLATE FOR MAKEFILE TO USE IN FRAMA-C/EVA CASE STUDIES

# DO NOT EDIT THE LINES BETWEEN THE '#'S

###############################################################################
# Improves analysis time, at the cost of extra memory usage
export FRAMA_C_MEMORY_FOOTPRINT = 8
#
# frama-c-path.mk contains variables which are specific to each
# user and should not be versioned, such as the path to the
# frama-c binaries (e.g. FRAMAC and FRAMAC_GUI).
# It is an optional include, unnecessary if frama-c is in the PATH
-include frama-c-path.mk
#
# FRAMAC_CONFIG is defined in frama-c-path.mk when it is included, so the
# line below will be safely ignored if this is the case
FRAMAC_CONFIG ?= frama-c-config
#
# frama-c.mk contains the main rules and targets
-include $(shell $(FRAMAC_CONFIG) -print-share-path)/analysis-scripts/frama-c.mk
#
###############################################################################

# EDIT VARIABLES AND TARGETS BELOW AS NEEDED
# The flags below are only suggestions to use with Eva, and can be removed

FRAMAC_SHARE = $(shell $(FRAMAC_CONFIG) -print-share-path)

# (Optional) preprocessing flags, usually handled by -json-compilation-database
CPPFLAGS    += \
  -include__fc_builtin.h \
  -D_POSIX_C_SOURCE=200809L \

# (Optional) Frama-C general flags (parsing and kernel)
FCFLAGS     += \
  -main eva_main \

# (Optional) Eva-specific flags
EVAFLAGS    += \
  -eva-ilevel 16 \

# (MANDATORY) Name of the main target
MAIN_TARGET := hiredis-format

# Add other targets if needed
TARGETS = $(MAIN_TARGET).eva hiredis-misc.eva

TEST_SRCS := \
  $(sort $(wildcard *.c)) \
  $(FRAMAC_SHARE)/libc/string.c \
  $(FRAMAC_SHARE)/libc/netdb.c \

# Default target
all: $(TARGETS)

hiredis-format.parse: CPPFLAGS += -DEVA_TEST_FORMAT
hiredis-format.parse: $(TEST_SRCS)

hiredis-misc.parse: CPPFLAGS += -DEVA_TEST_MISC
hiredis-misc.parse: $(TEST_SRCS)

hiredis-tcp.parse: CPPFLAGS += -DEVA_TEST_TCP
hiredis-tcp.parse: $(TEST_SRCS)

hiredis-unix.parse: CPPFLAGS += -DEVA_TEST_UNIX
hiredis-unix.parse: $(TEST_SRCS)

hiredis-tcp-long.parse: CPPFLAGS += -DEVA_TEST_TCP -DEVA_TEST_BLOCKING_LONG
hiredis-tcp-long.parse: $(TEST_SRCS)

hiredis-unix-long.parse: CPPFLAGS += -DEVA_TEST_UNIX -DEVA_TEST_BLOCKING_LONG
hiredis-unix-long.parse: $(TEST_SRCS)

# The following targets are optional and provided for convenience only
parse: $(TARGETS:%.eva=%.parse)
gui: $(MAIN_TARGET).eva.gui

stats: $(TARGETS:%.eva=%.parse) $(TARGETS)
	../show_stats.sh "$(notdir $(CURDIR))" $^
