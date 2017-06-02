# frama-c-path.mk contains variables which are specific to each
# user and should not be versioned, such as the path to the
# frama-c binaries (e.g. FRAMAC and FRAMAC_GUI).
# It is an optional include, unnecessary if frama-c is in the PATH.
-include frama-c-path.mk

include ../fcscripts/frama-c.mk

# Define global parameters
CPPFLAGS         +=
FCFLAGS          +=
EVAFLAGS         += -plevel 256 -val-malloc-functions calloc,alloc -val-builtin calloc:Frama_C_calloc_fresh -val-print-callstacks
-include manually_optimized.loop

# Export environment variable for Frama-C
export FRAMA_C_MEMORY_FOOTPRINT = 8

TARGETS=monocypher1 monocypher2 monocypher3 monocypher4 monocypher5 monocypher6 \
	monocypher7 monocypher8 monocypher9 monocypher10 monocypher11 monocypher12 \
	monocypher13 monocypher14 monocypher15 monocypher16 monocypher17
all: $(TARGETS:%=%.eva)
help:
	@echo "targets: $(TARGETS)"
loop: $(TARGETS:%=%.parse.loop) $(TARGETS:%=%.eva.loop)

monocypher1.parse: monocypher.c sha512.c test.c
monocypher2.parse: monocypher.c sha512.c test.c
monocypher3.parse: monocypher.c sha512.c test.c
monocypher4.parse: monocypher.c sha512.c test.c
monocypher5.parse: monocypher.c sha512.c test.c
monocypher6.parse: monocypher.c sha512.c test.c
monocypher7.parse: monocypher.c sha512.c test.c
monocypher8.parse: monocypher.c sha512.c test.c
monocypher9.parse: monocypher.c sha512.c test.c
monocypher10.parse: monocypher.c sha512.c test.c
monocypher11.parse: monocypher.c sha512.c test.c
monocypher12.parse: monocypher.c sha512.c test.c
monocypher13.parse: monocypher.c sha512.c test.c
monocypher14.parse: monocypher.c sha512.c test.c
monocypher15.parse: monocypher.c sha512.c test.c
monocypher16.parse: monocypher.c sha512.c test.c
monocypher17.parse: monocypher.c sha512.c test.c
monocypher_all.parse: monocypher.c sha512.c test.c

monocypher1.parse: FCFLAGS+=-cpp-extra-args="-DFC_TEST_1"
monocypher2.parse: FCFLAGS+=-cpp-extra-args="-DFC_TEST_2"
monocypher3.parse: FCFLAGS+=-cpp-extra-args="-DFC_TEST_3"
monocypher4.parse: FCFLAGS+=-cpp-extra-args="-DFC_TEST_4"
monocypher5.parse: FCFLAGS+=-cpp-extra-args="-DFC_TEST_5"
monocypher6.parse: FCFLAGS+=-cpp-extra-args="-DFC_TEST_6"
monocypher7.parse: FCFLAGS+=-cpp-extra-args="-DFC_TEST_7"
monocypher8.parse: FCFLAGS+=-cpp-extra-args="-DFC_TEST_8"
monocypher9.parse: FCFLAGS+=-cpp-extra-args="-DFC_TEST_9"
monocypher10.parse: FCFLAGS+=-cpp-extra-args="-DFC_TEST_10"
monocypher11.parse: FCFLAGS+=-cpp-extra-args="-DFC_TEST_11"
monocypher12.parse: FCFLAGS+=-cpp-extra-args="-DFC_TEST_12"
monocypher13.parse: FCFLAGS+=-cpp-extra-args="-DFC_TEST_13"
monocypher14.parse: FCFLAGS+=-cpp-extra-args="-DFC_TEST_14"
monocypher15.parse: FCFLAGS+=-cpp-extra-args="-DFC_TEST_15"
monocypher16.parse: FCFLAGS+=-cpp-extra-args="-DFC_TEST_16"
monocypher17.parse: FCFLAGS+=-cpp-extra-args="-DFC_TEST_17"
monocypher_all.parse: FCFLAGS+=-cpp-extra-args="-DFC_TEST_ALL"
