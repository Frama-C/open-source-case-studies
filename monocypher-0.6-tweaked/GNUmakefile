# frama-c-path.mk contains variables which are specific to each
# user and should not be versioned, such as the path to the
# frama-c binaries (e.g. FRAMAC and FRAMAC_GUI).
# It is an optional include, unnecessary if frama-c is in the PATH.
-include frama-c-path.mk

FRAMAC_CONFIG ?= frama-c-config
include $(shell $(FRAMAC_CONFIG) -print-share-path)/analysis-scripts/frama-c.mk

# Define global parameters
CPPFLAGS         +=
FCFLAGS          +=
EVAFLAGS         += -plevel 256 -val-malloc-functions calloc,alloc -val-builtin calloc:Frama_C_calloc_fresh -val-print-callstacks
-include monocypher.slevel

# Export environment variable for Frama-C
export FRAMA_C_MEMORY_FOOTPRINT = 8

TARGETS=monocypher1 monocypher2 monocypher3 monocypher4 monocypher5 monocypher6 \
	monocypher7 monocypher8 monocypher9 monocypher10 monocypher11 monocypher12 \
	monocypher13 monocypher14 monocypher15 monocypher16 monocypher17
all: $(TARGETS:%=%.eva)
help:
	@echo "targets: $(TARGETS)"
loop: $(TARGETS:%=%.parse.loop) $(TARGETS:%=%.eva.loop)
parse: $(TARGETS:%=%.parse)
stats: $(TARGETS:%=%.parse) $(TARGETS:%=%.eva)
	../show_stats.sh "$(notdir $(CURDIR))" $^

$(TARGETS:%=%.parse) monocypher_all.parse: monocypher.c sha512.c test.c

monocypher1.parse: CPPFLAGS+=-DFC_TEST_1
monocypher2.parse: CPPFLAGS+=-DFC_TEST_2
monocypher3.parse: CPPFLAGS+=-DFC_TEST_3
monocypher4.parse: CPPFLAGS+=-DFC_TEST_4
monocypher5.parse: CPPFLAGS+=-DFC_TEST_5
monocypher6.parse: CPPFLAGS+=-DFC_TEST_6
monocypher7.parse: CPPFLAGS+=-DFC_TEST_7
monocypher8.parse: CPPFLAGS+=-DFC_TEST_8
monocypher9.parse: CPPFLAGS+=-DFC_TEST_9
monocypher10.parse: CPPFLAGS+=-DFC_TEST_10
monocypher11.parse: CPPFLAGS+=-DFC_TEST_11
monocypher12.parse: CPPFLAGS+=-DFC_TEST_12
monocypher13.parse: CPPFLAGS+=-DFC_TEST_13
monocypher14.parse: CPPFLAGS+=-DFC_TEST_14
monocypher15.parse: CPPFLAGS+=-DFC_TEST_15
monocypher16.parse: CPPFLAGS+=-DFC_TEST_16
monocypher17.parse: CPPFLAGS+=-DFC_TEST_17
monocypher_all.parse: CPPFLAGS+=-DFC_TEST_ALL
