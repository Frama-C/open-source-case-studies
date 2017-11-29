# frama-c-path.mk contains variables which are specific to each
# user and should not be versioned, such as the path to the
# frama-c binaries (e.g. FRAMAC and FRAMAC_GUI).
# It is an optional include, unnecessary if frama-c is in the PATH.
-include frama-c-path.mk

FRAMAC_CONFIG ?= frama-c-config
include $(shell $(FRAMAC_CONFIG) -print-share-path)/analysis-scripts/frama-c.mk

# Define global parameters
CPPFLAGS         += -I include -I $($FRAMAC_BIN -print-path)/libc
FCFLAGS          +=
USE_SPEC         += \
  my_set_session \
  my_get_session \
  aes_setkey_enc \
  aes_setkey_dec \
  aes_crypt_cbc \
  des3_crypt_ecb \
  des3_crypt_cbc \
  des_setkey \
  arc4_crypt \
  ssl_free \
  x509_free \
  x509parse_crt \
  x509parse_key \
  x509parse_verifycrl \
  hardclock \
  sha4_update \
  sha4_process \
  sha1_process \
  sha1_finish \
  aes_crypt_ecb \
  md5_process \
  ctr_drbg_random \
  dhm_check_range \
  dhm_make_params \
  mpi_free \
  mpi_exp_mod \
  mpi_fill_random \
  mpi_read_string \
  mpi_read_binary \
  mpi_msb \
  mpi_write_binary \
  mpi_cmp_mpi \
  mpi_cmp_abs \
  mpi_copy \
  mpi_sub_mpi \
  mpi_mod_mpi \
  mpi_mul_mpi \
  mpi_add_abs \
  mpi_sub_abs \
  camellia_crypt_cbc \
  camellia_feistel \
  sha4
EVAFLAGS         += \
  -val-subdivide-non-linear 16 \
  -val-ilevel 13 \
  -no-val-malloc-returns-null \
  -val-use-spec $(call fc_list,$(USE_SPEC))

# Export environment variable for Frama-C
export FRAMA_C_MEMORY_FOOTPRINT	= 8

TARGETS=ssl_server
all: $(TARGETS:%=%.eva)
help:
	@echo "targets: $(TARGETS)"
loop: $(TARGETS:%=%.parse.loop) $(TARGETS:%=%.eva.loop)
parse: $(TARGETS:%=%.parse)
stats: $(TARGETS:%=%.parse) $(TARGETS:%=%.eva)
	../show_stats.sh "$(notdir $(CURDIR))" $^

ssl_server.parse: stubs.h $(sort $(wildcard library/*.c)) programs/ssl/ssl_server.c
ssl_server.eva: EVAFLAGS+=$(shell cat ssl_server.slevel | tr -d '\n\\')
