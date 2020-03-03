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

# (Optional) preprocessing flags, usually handled by -json-compilation-database
CPPFLAGS    +=

# (Optional) Frama-C general flags (parsing and kernel)
FCFLAGS     += \
  -kernel-warn-key annot:missing-spec=abort \
  -kernel-warn-key typing:implicit-function-declaration=abort \

# (Optional) Eva-specific flags
EVAFLAGS    += \
  -eva-warn-key builtins:missing-spec=abort \

TARGETS = cwe20.eva cwe119.eva cwe190.eva cwe416.eva cwe787.eva

PRECISE_TARGETS = $(subst .eva,-precise.eva,$(TARGETS))

# Default target
all: $(TARGETS) $(PRECISE_TARGETS)
help:
	@echo "targets: $(TARGETS) $(PRECISE_TARGETS)"
display-targets:
	@echo "$(TARGETS) $(PRECISE_TARGETS)"

cwe20.parse:  cwe20.c
cwe119.parse: cwe119.c
cwe190.parse: cwe190.c
cwe416.parse: cwe416.c
cwe787.parse: cwe787.c

cwe20-precise.parse:  cwe20.c
cwe119-precise.parse: cwe119.c
cwe190-precise.parse: cwe190.c
cwe416-precise.parse: cwe416.c
cwe787-precise.parse: cwe787.c

cwe20-precise.eva:  EVAFLAGS +=
cwe119-precise.eva: EVAFLAGS += -eva-precision 1
cwe190-precise.eva: EVAFLAGS += -warn-unsigned-overflow -eva-no-alloc-returns-null
cwe416-precise.eva: EVAFLAGS += -eva-precision 1
cwe787-precise.eva: EVAFLAGS += -eva-precision 2 -eva-no-alloc-returns-null

# The following targets are optional and provided for convenience only
parse: $(TARGETS:%.eva=%.parse)

stats: $(TARGETS:%.eva=%.parse) $(TARGETS)
	../show_stats.sh "$(notdir $(CURDIR))" $^
