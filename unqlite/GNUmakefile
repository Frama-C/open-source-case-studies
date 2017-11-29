# frama-c-path.mk contains variables which are specific to each
# user and should not be versioned, such as the path to the
# frama-c binaries (e.g. FRAMAC and FRAMAC_GUI).
# It is an optional include, unnecessary if frama-c is in the PATH.
-include frama-c-path.mk

FRAMAC_CONFIG ?= frama-c-config
include $(shell $(FRAMAC_CONFIG) -print-share-path)/analysis-scripts/frama-c.mk

# Define global parameters
CPPFLAGS     = -includefc_compatibility.h -D__USE_MISC -D_BSD_SOURCE
FCFLAGS     += -machdep x86_64
# NOTE: unqlite has several recursive calls that are not supported by Eva;
# the stubs added to several functions are unsound and serve only to allow the
# analysis to proceed. This case study is only for non-regression purposes and
# does not represent the behavior of the actual code.
EVAFLAGS    += -no-val-malloc-returns-null -main eva_main \
               -val-use-spec SyMemBackendFree,SyMemBackendPoolFree,SyMemBackendRelease,pager_release_page,lhCursorReset,pager_shared_lock,unqliteGenError,unqliteOsLock,unqliteOsUnlock,unqliteOsDelete,unqliteOsOpen,pager_wait_on_lock,pager_write_db_header,SyMemBackendRealloc

# Export environment variable for Frama-C
export FRAMA_C_MEMORY_FOOTPRINT	= 8

TARGETS=unqlite_tar
#     unqlite_const_intro \
#     unqlite_csr_intro \
#     unqlite_doc_intro \
#     unqlite_doc_io_intro \
#     unqlite_func_intro \
#     unqlite_hostapp_info \
#     unqlite_huge_insert \
#     unqlite_kv_intro \
#     unqlite_mp3_tag \

all: $(TARGETS:%=%.eva)
help:
	@echo "targets: $(TARGETS)"
loop: $(TARGETS:%=%.parse.loop) $(TARGETS:%=%.eva.loop)
parse: $(TARGETS:%=%.parse)
stats: $(TARGETS:%=%.parse) $(TARGETS:%=%.eva)
	../show_stats.sh "$(notdir $(CURDIR))" $^

#unqlite_const_intro.parse: unqlite.c unqlite_const_intro.c
#unqlite_csr_intro.parse: unqlite.c unqlite_csr_intro.c
#unqlite_doc_intro.parse: unqlite.c unqlite_doc_intro.c
#unqlite_doc_io_intro.parse: unqlite.c unqlite_doc_io_intro.c
#unqlite_func_intro.parse: unqlite.c unqlite_func_intro.c
#unqlite_hostapp_info.parse: unqlite.c unqlite_hostapp_info.c
#unqlite_huge_insert.parse: unqlite.c unqlite_huge_insert.c
#unqlite_kv_intro.parse: unqlite.c unqlite_kv_intro.c
#unqlite_mp3_tag.parse: unqlite.c unqlite_mp3_tag.c
unqlite_tar.parse: unqlite.c unqlite_tar.c stubs.c
