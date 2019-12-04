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

# (Optional) preprocessing flags, usually handled by -json-compilation-database
CPPFLAGS    += -Isrc -Isrc/optional

# (Optional) Frama-C general flags (parsing and kernel)
FCFLAGS     += \
  -machdep x86_64 \
  -no-warn-signed-overflow \

# msg key callstack is too unstable and causes oracle changes more often than
# 
# -kernel-msg-key callstack \

# (Optional) Eva-specific flags
EVAFLAGS    += \
  -slevel 8 \
  -eva-split-return auto \

# -eva-gauges-domain : -6 alarms, +1m30 analysis time
# -eva-equality-domain : +3 alarms (!), +1m30 analysis time

#FCGUIFLAGS += -kernel-msg-key callstack

# (MANDATORY) Name of the main target
MAIN_TARGET := monocypher

# Add other targets if needed
TARGETS = $(MAIN_TARGET).eva

# Default target
all: $(TARGETS)
help:
	@echo "targets: $(TARGETS)"
display-targets:
	@echo "$(TARGETS)"

# (MANDATORY) List of source files used by MAIN_TARGET, usually obtained
# via a JSON compilation database + analysis-scripts/list_files.py
$(MAIN_TARGET).parse: src/monocypher.c src/optional/sha512.c tests/test.c


# The following targets are optional and provided for convenience only
parse: $(TARGETS:%.eva=%.parse)
gui: $(MAIN_TARGET).eva.gui

stats: $(TARGETS:%.eva=%.parse) $(TARGETS)
	../show_stats.sh "$(notdir $(CURDIR))" $^
