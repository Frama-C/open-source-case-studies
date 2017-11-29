# frama-c-path.mk contains variables which are specific to each
# user and should not be versioned, such as the path to the
# frama-c binaries (e.g. FRAMAC and FRAMAC_GUI).
# It is an optional include, unnecessary if frama-c is in the PATH.
-include frama-c-path.mk

FRAMAC_CONFIG ?= frama-c-config
include $(shell $(FRAMAC_CONFIG) -print-share-path)/analysis-scripts/frama-c.mk

# Define global parameters
CPPFLAGS  = -include$(shell $(FRAMAC) -print-path)/libc/string.h
FCFLAGS  +=
EVAFLAGS +=

# Export environment variable for Frama-C
export FRAMA_C_MEMORY_FOOTPRINT	= 8

TARGETS=compress decompress stream-compress stream-decompress
all: $(TARGETS:%=%.eva)
help:
	@echo "targets: $(TARGETS)"
loop: $(TARGETS:%=%.parse.loop) $(TARGETS:%=%.eva.loop)
parse: $(TARGETS:%=%.parse)
stats: $(TARGETS:%=%.parse) $(TARGETS:%=%.eva)
	../show_stats.sh "$(notdir $(CURDIR))" $^

compress.parse: compress_file.c quicklz.c

decompress.parse: decompress_file.c quicklz.c

stream-compress.parse: CPPFLAGS += -DQLZ_COMPRESSION_LEVEL=3 -DQLZ_STREAMING_BUFFER=10000
stream-compress.parse: stream_compress.c quicklz.c

stream-decompress.parse: CPPFLAGS += -DQLZ_COMPRESSION_LEVEL=3 -DQLZ_STREAMING_BUFFER=10000
stream-decompress.parse: stream_decompress.c quicklz.c
