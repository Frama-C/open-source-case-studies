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
  addrfilt.c \
  array.c \
  clientlog.c \
  cmdparse.c \
  conf.c \
  hash_intmd5.c \
  keys.c \
  local.c \
  logging.c \
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

CPPFLAGS    += -D_XOPEN_SOURCE=200112L -DNB_TESTS=3 -includefc_stubs.h

FCFLAGS     += -machdep gcc_x86_64 \
  -kernel-warn-error typing:implicit-function-declaration \
  -warn-special-float none

# (Optional) EVA-specific flags
EVAFLAGS    += \
  -val-use-spec atoi,malloc,free,calloc,Transform,parse_include \
  -eva-equality-domain -eva-gauges-domain -eva-symbolic-locations-domain \
  -slevel 5 \
  -val-warn-on-alarms \
  -val-malloc-functions malloc,realloc,Malloc,Malloc2,Realloc,Realloc2

# Add other targets if needed, e.g. 'regress'. The name does not have to
# correspond to an existing file.
TARGETS = ntp_core regress

# Default target
all: $(TARGETS:%=%.eva)

# For each target, you MUST add a <target>.parse rule listing the sources
# used by the target; you MAY add a <target>.eva rule with specific options
# for EVA.

ntp_core.parse: $(TEST_COMMON_SRCS) test/unit/ntp_core.c
ntp_core.eva: EVAFLAGS += -main eva_main \
  $(shell cat ntp_core.slevel | tr -d '\n\\')

# The following parsing rule reuses variable TEST_COMMON_SRCS to avoid
# having to manually list the sources. Note that the unit test version of
# regress.c redefines some functions from the other regress.c file, so
# we remove the latter from the list of sources.
regress.parse: $(filter-out regress.c,$(TEST_COMMON_SRCS)) test/unit/regress.c
regress.eva: EVAFLAGS += -main eva_main -slevel 100

# The following targets are optional and provided for convenience only
help:
	@echo "targets: $(TARGETS)"
loop: $(TARGETS:%=%.parse.loop) $(TARGETS:%=%.eva.loop)
parse: $(TARGETS:%=%.parse)
stats: $(TARGETS:%=%.parse) $(TARGETS:%=%.eva)
	../show_stats.sh "$(notdir $(CURDIR))" $^
