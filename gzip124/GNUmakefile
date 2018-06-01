# frama-c-path.mk contains variables which are specific to each
# user and should not be versioned, such as the path to the
# frama-c binaries (e.g. FRAMAC and FRAMAC_GUI).
# It is an optional include, unnecessary if frama-c is in the PATH.
-include frama-c-path.mk

FRAMAC_CONFIG ?= frama-c-config
include $(shell $(FRAMAC_CONFIG) -print-share-path)/analysis-scripts/frama-c.mk

# Define global parameters
CPPFLAGS  = -include$(shell $(FRAMAC) -print-path)/libc/string.h \
            -include../__fc_compatibility.h \
            -DSTDC_HEADERS=1 -DHAVE_UNISTD_H=1 -DDIRENT=1 -DNO_UTIME=1 \
            -I$(shell $(FRAMAC) -print-path)/libc -I$(DIR)/

FCFLAGS  += -nonterm-ignore abort,do_exit,exit
EVAFLAGS += -slevel 2 -no-val-alloc-returns-null -no-val-builtins-auto

# Export environment variable for Frama-C
export FRAMA_C_MEMORY_FOOTPRINT	= 8

TARGETS=gzip
all: $(TARGETS:%=%.eva)
help:
	@echo "targets: $(TARGETS)"
loop: $(TARGETS:%=%.parse.loop) $(TARGETS:%=%.eva.loop)
parse: $(TARGETS:%=%.parse)
stats: $(TARGETS:%=%.parse) $(TARGETS:%=%.eva)
	../show_stats.sh "$(notdir $(CURDIR))" $^

gzip.parse: gzip.c zip.c deflate.c trees.c bits.c unzip.c inflate.c util.c \
              crypt.c lzw.c unlzw.c unpack.c unlzh.c getopt.c
