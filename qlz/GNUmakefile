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
CPPFLAGS += -include$(shell $(FRAMAC) -print-path)/libc/string.h

# (Optional) Frama-C general flags (parsing and kernel)
FCFLAGS  += \
  -main eva_main \

# (Optional) Eva-specific flags
EVAFLAGS    += \
  -eva-no-alloc-returns-null \

# (MANDATORY) Name of the main target
MAIN_TARGET := compress

# Add other targets if needed
TARGETS = $(MAIN_TARGET).eva decompress.eva stream-compress.eva stream-decompress.eva

# Default target
all: $(TARGETS)

# (MANDATORY) List of source files used by MAIN_TARGET, usually obtained
# via a JSON compilation database + analysis-scripts/list_files.py
$(MAIN_TARGET).parse: compress_file.c quicklz.c fc_stubs.c

decompress.parse: decompress_file.c quicklz.c fc_stubs.c

stream-compress.parse: CPPFLAGS += -DQLZ_COMPRESSION_LEVEL=3 -DQLZ_STREAMING_BUFFER=10000
stream-compress.parse: stream_compress.c quicklz.c fc_stubs.c

stream-decompress.parse: CPPFLAGS += -DQLZ_COMPRESSION_LEVEL=3 -DQLZ_STREAMING_BUFFER=10000
stream-decompress.parse: stream_decompress.c quicklz.c fc_stubs.c

# The following targets are optional and provided for convenience only
parse: $(TARGETS:%.eva=%.parse)
loop: $(TARGETS:%.eva=%.parse.loop) $(TARGETS:%=%.loop)
gui: $(MAIN_TARGET).eva.gui

# Run 'make <TARGET>.eva.loop' to obtain a .loop file, fine-tune it by hand,
# then rename it to <TARGET>.slevel to prevent it from being overwritten.
# If such file exists, use it to define per-function slevel values.
ifneq (,$(wildcard $(MAIN_TARGET).slevel))
$(MAIN_TARGET).eva: \
  EVAFLAGS += $(shell cat $(MAIN_TARGET).slevel | tr -d '\n\\')
endif
