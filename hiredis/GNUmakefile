# frama-c-path.mk contains variables which are specific to each
# user and should not be versioned, such as the path to the
# frama-c binaries (e.g. FRAMAC and FRAMAC_GUI).
# It is an optional include, unnecessary if frama-c is in the PATH.
-include frama-c-path.mk

FRAMAC_CONFIG ?= frama-c-config
FRAMAC_SHARE = $(shell $(FRAMAC_CONFIG) -print-share-path)
include $(FRAMAC_SHARE)/analysis-scripts/frama-c.mk

# Define global parameters
CPPFLAGS     = -include../__fc_compatibility.h -include__fc_builtin.h \
  -D_POSIX_C_SOURCE=200809L
FCFLAGS     += -main eva_main
EVAFLAGS    +=

# Export environment variable for Frama-C
export FRAMA_C_MEMORY_FOOTPRINT	= 8

TARGETS=\
hiredis_test_format \
hiredis_test_misc \

# some targets are disabled from automatic testing until further tuning
#hiredis_test_tcp \
#hiredis_test_unix \
#hiredis_test_tcp_long \
#hiredis_test_unix_long

all: $(TARGETS:%=%.eva)
help:
	@echo "targets: $(TARGETS)"
loop: $(TARGETS:%=%.parse.loop) $(TARGETS:%=%.eva.loop)
parse: $(TARGETS:%=%.parse)
stats: $(TARGETS:%=%.parse) $(TARGETS:%=%.eva)
	../show_stats.sh "$(notdir $(CURDIR))" $^

TEST_SRCS:=$(sort $(wildcard *.c)) $(FRAMAC_SHARE)/libc/string.c \
  $(FRAMAC_SHARE)/libc/netdb.c

hiredis_test_format.parse: CPPFLAGS += -DEVA_TEST_FORMAT
hiredis_test_format.parse: $(TEST_SRCS)

hiredis_test_misc.parse: CPPFLAGS += -DEVA_TEST_MISC
hiredis_test_misc.parse: $(TEST_SRCS)

hiredis_test_tcp.parse: CPPFLAGS += -DEVA_TEST_TCP
hiredis_test_tcp.parse: $(TEST_SRCS)

hiredis_test_unix.parse: CPPFLAGS += -DEVA_TEST_UNIX
hiredis_test_unix.parse: $(TEST_SRCS)

hiredis_test_tcp_long.parse: \
  CPPFLAGS += -DEVA_TEST_TCP -DEVA_TEST_BLOCKING_LONG
hiredis_test_tcp_long.parse: $(TEST_SRCS)

hiredis_test_unix_long.parse: \
  CPPFLAGS += -DEVA_TEST_UNIX -DEVA_TEST_BLOCKING_LONG
hiredis_test_unix_long.parse: $(TEST_SRCS)
