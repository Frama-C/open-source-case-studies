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
CPPFLAGS    += -CC
# -CC is used to preserve loop unroll annotations from expanded macros

# (Optional) Frama-C general flags (parsing and kernel)
FCFLAGS     += \
  -json-compilation-database . \

# (Optional) Eva-specific flags
EVAFLAGS    += \
  -eva-subdivide-non-linear 16 \
  -eva-ilevel 13 \
  -eva-no-alloc-returns-null \
  -eva-use-spec $(call fc_list,$(USE_SPEC)) \
  -eva-slevel 2 \

USE_SPEC  += \
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
  sha4 \

# (MANDATORY) Name of the main target
MAIN_TARGET := polarssl-server

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
$(MAIN_TARGET).parse: \
  stubs.h \
  $(sort $(wildcard library/*.c)) \
  programs/ssl/ssl_server.c \

# The following targets are optional and provided for convenience only
parse: $(TARGETS:%.eva=%.parse)
gui: $(MAIN_TARGET).eva.gui

stats: $(TARGETS:%.eva=%.parse) $(TARGETS)
	../show_stats.sh "$(notdir $(CURDIR))" $^
