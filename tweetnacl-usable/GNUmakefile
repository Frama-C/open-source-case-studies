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
SLEVEL_FUNCTION  += \
  crypto_scalarmult_curve25519_tweet:32 \
  crypto_stream_salsa20_tweet_xor:64 \
  M:256 \
  Z:16 \
  add1305:17 \
  crypto_onetimeauth_poly1305_tweet:1600 \
  core:320 \
  pack25519:30,unpack25519:16 \
  inv25519:16,car25519:16
MERGE_AFTER_LOOP += \
  core \
  pack25519 \
  crypto_onetimeauth_poly1305_tweet \
  inv25519

EVAFLAGS         += \
  -no-val-alloc-returns-null \
  -no-warn-signed-overflow -slevel 16 \
  -slevel-function $(call fc_list,$(SLEVEL_FUNCTION)) \
  -val-slevel-merge-after-loop $(call fc_list,$(MERGE_AFTER_LOOP))

# Export environment variable for Frama-C
export FRAMA_C_MEMORY_FOOTPRINT	= 8

TARGETS=main
all: $(TARGETS:%=%.eva)
help:
	@echo "targets: $(TARGETS)"
loop: $(TARGETS:%=%.parse.loop) $(TARGETS:%=%.eva.loop)
parse: $(TARGETS:%=%.parse)
stats: $(TARGETS:%=%.parse) $(TARGETS:%=%.eva)
	../show_stats.sh "$(notdir $(CURDIR))" $^

main.parse: main.c tweetnacl.c randombytes.c
