# frama-c-path.mk contains variables which are specific to each
# user and should not be versioned, such as the path to the
# frama-c binaries (e.g. FRAMAC and FRAMAC_GUI).
# It is an optional include, unnecessary if frama-c is in the PATH.
-include frama-c-path.mk

include ../fcscripts/frama-c.mk

# Define global parameters
CPPFLAGS         += -I include -I $($FRAMAC_BIN -print-path)/libc
FCFLAGS          +=
SLEVEL_FUNCTION  += \
  aes_setkey_enc:256 \
  aes_crypt_ecb:100 \
  aes_gen_tables:256 \
  arc4_setup:256 \
  sha1_update:100 \
  rsa_pkcs1_decrypt:1000 \
  md5_update:100 \
  md5_hmac_starts:65 \
  camellia_crypt_cbc:900 \
  camellia_setkey_enc:21 \
  camellia_setkey_dec:51 \
  ssl_encrypt_buf:100 \
  ssl_decrypt_buf:100 \
  sha4_update:130 \
  sha4_process:100 \
  block_cipher_df:1000 \
  ssl_derive_keys:40 \
  ctr_drbg_random_with_add:1000 \
  ctr_drbg_update_internal:100 \
  des3_set3key:32 \
  entropy_func:5515 \
  entropy_update:64 \
  platform_entropy_poll:130 \
  entropy_gather:100 \
  ssl_parse_client_hello:100 \
  strlen:2000 \
  ssl_fetch_input:100 \
  ssl_read_record:100 \
  sha1_hmac_starts:64 \
  tls1_prf:6000 \
  ssl_write_certificate:10
MERGE_AFTER_LOOP += \
  sha4_process aes_gen_tables \
  sha4_update,ssl_decrypt_buf \
  entropy_func \
  ctr_drbg_random_with_add \
  ssl_parse_client_hello \
  camellia_setkey_enc \
  camellia_setkey_dec \
  arc4_setup
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
  -slevel-function $(call fc_list,$(SLEVEL_FUNCTION)) \
  -val-slevel-merge-after-loop $(call fc_list,$(MERGE_AFTER_LOOP)) \
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

ssl_server.parse: stubs.h $(sort $(wildcard library/*.c)) programs/ssl/ssl_server.c
