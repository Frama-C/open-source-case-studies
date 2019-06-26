# DO NOT EDIT THE LINES BETWEEN THE '#'S
###############################################################################
# Improves analysis time, at the price of extra memory usage
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
# frama-c.mk should be included at the top of your Makefile, right below
# the inclusion of frama-c-path.mk
-include $(shell $(FRAMAC_CONFIG) -print-share-path)/analysis-scripts/frama-c.mk
###############################################################################

# EDIT VARIABLES AND TARGETS BELOW AS NEEDED

TEST_COMMON_SRCS = test/unit/test.c \
  $(shell $(FRAMAC_CONFIG) -print-share-path)/libc/string.c \
  $(shell $(FRAMAC_CONFIG) -print-share-path)/libc/stdlib.c \
  $(shell $(FRAMAC_CONFIG) -print-share-path)/libc/stdio.c \
  $(shell $(FRAMAC_CONFIG) -print-share-path)/libc/glob.c \
  $(shell $(FRAMAC_CONFIG) -print-share-path)/libc/netdb.c \
  addrfilt.c \
  array.c \
  clientlog.c \
  cmdparse.c \
  conf.c \
  hash_intmd5.c \
  keys.c \
  local.c \
  memory.c \
  nameserv.c \
  ntp_io.c \
  reference.c \
  regress.c \
  sched.c \
  smooth.c \
  sources.c \
  sourcestats.c \
  util.c \
  fc_stubs.c \
  stubs.c \

# logging.c voluntarily ommitted, to skip analyzing logging functions

CPPFLAGS    += -D_XOPEN_SOURCE=200112L -DNB_TESTS=3

FCFLAGS     += -machdep gcc_x86_64 \
  -warn-special-float none \
  -kernel-warn-key typing:implicit-function-declaration=abort \

# (Optional) EVA-specific flags
EVAFLAGS    += \
  -eva-use-spec atoi,malloc,free,calloc,Transform,parse_include,SCH_AddTimeout \
  -eva-equality-domain -eva-gauges-domain -eva-symbolic-locations-domain \
  -eva-warn-key=alarm \
  -eva-malloc-functions malloc,realloc,Malloc,Malloc2,Realloc,Realloc2 \
  -eva-warn-key builtins:missing-spec=abort \
  -eva-warn-key malloc:weak \

MAIN_TARGET := chrony-ntp-core

TARGETS = $(MAIN_TARGET).eva chrony-regress.eva

# Default target
all: $(TARGETS)

chrony-ntp-core.parse: $(TEST_COMMON_SRCS) test/unit/ntp_core.c
chrony-ntp-core.eva: EVAFLAGS += -main eva_main \

# The following parsing rule reuses variable TEST_COMMON_SRCS to avoid
# having to manually list the sources. Note that the unit test version of
# regress.c redefines some functions from the other regress.c file, so
# we remove the latter from the list of sources.
chrony-regress.parse: \
  $(filter-out regress.c,$(TEST_COMMON_SRCS)) test/unit/regress.c
chrony-regress.eva: EVAFLAGS += -main eva_main

# The following targets are optional and provided for convenience only
help:
	@echo "targets: $(TARGETS)"
display-targets:
	@echo "$(TARGETS)"
loop: $(TARGETS:%.eva=%.parse.loop) $(TARGETS:%=%.loop)
parse: $(TARGETS:%.eva=%.parse)
stats: $(TARGETS:%.eva=%.parse) $(TARGETS)
	../show_stats.sh "$(notdir $(CURDIR))" $^
