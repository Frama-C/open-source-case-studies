# frama-c-path.mk contains variables which are specific to each
# user and should not be versioned, such as the path to the
# frama-c binaries (e.g. FRAMAC and FRAMAC_GUI).
# It is an optional include, unnecessary if frama-c is in the PATH.
-include frama-c-path.mk

FRAMAC_CONFIG ?= frama-c-config
include $(shell $(FRAMAC_CONFIG) -print-share-path)/analysis-scripts/frama-c.mk

# Define global parameters
CPPFLAGS  = -include$(shell $(FRAMAC) -print-path)/libc/string.h \
            -DSTDC_HEADERS=1 -DHAVE_UNISTD_H=1 -DDIRENT=1 -DNO_UTIME=1 \
            -I$(shell $(FRAMAC) -print-path)/libc -I$(DIR)/

FCFLAGS  += \
  -nonterm-ignore do_exit \
  -main eva_main \

EVAFLAGS += \
  -slevel 4 \
  -eva-no-alloc-returns-null \
  -eva-no-builtins-auto \
  -eva-widening-delay 3 \
  -eva-widening-period 3 \

# Export environment variable for Frama-C
export FRAMA_C_MEMORY_FOOTPRINT	= 8

MAIN_TARGET := gzip124
TARGETS = $(MAIN_TARGET).eva
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

gzip124.parse: gzip.c zip.c deflate.c trees.c bits.c unzip.c inflate.c util.c \
              crypt.c lzw.c unlzw.c unpack.c unlzh.c getopt.c \
              $(shell $(FRAMAC_CONFIG) -print-share-path)/libc/stdlib.c \
              fc_stubs.c
