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
CPPFLAGS    +=

# (Optional) Frama-C general flags (parsing and kernel)
FCFLAGS     += \
  -warn-special-float none \

# (Optional) Eva-specific flags
EVAFLAGS    += \
  -slevel 16 \
  -eva-equality-domain \

# (MANDATORY) Name of the main target
MAIN_TARGET := icpc

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
$(MAIN_TARGET).parse: src/impls.c src/roco.c src/sim.c src/main.c


# The following targets are optional and provided for convenience only
parse: $(TARGETS:%.eva=%.parse)
gui: $(MAIN_TARGET).eva.gui

stats: $(TARGETS:%.eva=%.parse) $(TARGETS)
	../show_stats.sh "$(notdir $(CURDIR))" $^
