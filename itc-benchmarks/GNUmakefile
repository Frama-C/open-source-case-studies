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
# The flags below are only suggestions to use with Eva, and can be removed

# (Optional) preprocessing flags, usually handled by -json-compilation-database
CPPFLAGS    += -Iinclude

# (Optional) Frama-C general flags (parsing and kernel)
FCFLAGS     += \
  -kernel-warn-key annot:missing-spec=abort \
  -kernel-warn-key typing:implicit-function-declaration=abort \

# (Optional) Eva-specific flags
EVAFLAGS    += \
  -eva-warn-key builtins:missing-spec=abort \
  -slevel 121 \
  -eva-no-alloc-returns-null \
  -eva-mlevel 10 \
  -main eva_main \
  -eva-split-return-function memory_leak_007_func_001:-1 \

SUBDIR_SRCS=\
main.c \
bit_shift.c \
buffer_overrun_dynamic.c \
buffer_underrun_dynamic.c \
cmp_funcadr.c \
conflicting_cond.c \
data_lost.c \
data_overflow.c \
data_underflow.c \
dead_code.c \
dead_lock.c \
deletion_of_data_structure_sentinel.c \
double_free.c \
double_release.c \
endless_loop.c \
free_nondynamic_allocated_memory.c \
free_null_pointer.c \
function_return_value_unchecked.c \
improper_termination_of_block.c \
insign_code.c \
invalid_extern_1.c \
invalid_extern.c \
invalid_memory_access.c \
littlemem_st.c \
livelock.c \
memory_allocation_failure.c \
memory_leak.c \
not_return.c \
null_pointer.c \
overrun_st.c \
ow_memcpy.c \
pow_related_errors.c \
ptr_subtraction.c \
redundant_cond.c \
return_local.c \
sign_conv.c \
sleep_lock.c \
st_overflow.c \
stubs.c \
st_underrun.c \
underrun_st.c \
uninit_memory_access.c \
uninit_pointer.c \
uninit_var.c \
unused_var.c \
zero_division.c \


# (MANDATORY) Name of the main target
MAIN_TARGET := 01_w_Defects

# Add other targets if needed
TARGETS = $(MAIN_TARGET).eva 02_wo_Defects.eva

# Default target
all: $(TARGETS)

01_w_Defects.parse: \
fc_stubs.c \
$(shell $(FRAMAC_CONFIG) -print-share-path)/libc/string.c \
$(foreach file,$(SUBDIR_SRCS),$(wildcard 01_w_Defects/$(file))) \

02_wo_Defects.parse: \
fc_stubs.c \
$(shell $(FRAMAC_CONFIG) -print-share-path)/libc/string.c \
$(foreach file,$(SUBDIR_SRCS),$(wildcard 02_wo_Defects/$(file))) \

# The following targets are optional and provided for convenience only
parse: $(TARGETS:%.eva=%.parse)
gui: $(MAIN_TARGET).eva.gui

stats: $(TARGETS:%.eva=%.parse) $(TARGETS)
	../show_stats.sh "$(notdir $(CURDIR))" $^
