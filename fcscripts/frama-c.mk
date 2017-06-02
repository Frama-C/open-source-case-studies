##########################################################################
#                                                                        #
#  Copyright (C) 2007-2017                                               #
#    CEA (Commissariat à l'énergie atomique et aux énergies              #
#         alternatives)                                                  #
#                                                                        #
#  you can redistribute it and/or modify it under the terms of the GNU   #
#  Lesser General Public License as published by the Free Software       #
#  Foundation, version 2.1.                                              #
#                                                                        #
#  It is distributed in the hope that it will be useful,                 #
#  but WITHOUT ANY WARRANTY; without even the implied warranty of        #
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         #
#  GNU Lesser General Public License for more details.                   #
#                                                                        #
#  See the GNU Lesser General Public License version 2.1                 #
#  for more details (enclosed in the file LICENSE).                      #
#                                                                        #
##########################################################################
#
# This file is intended to be included by a classic Makefile when doing
# non-trivial analyses with Frama-C and its EVA plugin. For instance, you
# can start your Makefile with the following line:
#
# include fcscripts/frama-c.mk
#
# This Makefile uses the following variables.
#
# FRAMAC        the frama-c binary
# FRAMAC_GUI    the frama-c gui binary
# CPPFLAGS      preprocessing flags
# FCFLAGS       general flags to use with frama-c
# EVAFLAGS      flags to use with the plugin$
# SLEVEL        the part of the frama-c command line concerning slevel
#               (you can use EVAFLAGS for this, if you don't intend
#               to use slevel-tweaker.sh)
#
# There are several ways to define or change these variables.
#
# With an environment variable:
#   export FRAMAC=~/bin/frama-c
#   make
#
# With command line arguments:
#   make FRAMAC=~/bin/frama-c
#
# In your Makefile, when you want to change a parameter for all analyses :
#   FCFLAGS += -verbose 2
#
# In your Makefile, for a single target :
#   target.eva: FCFLAGS += -main my_main
#
# In order to define an analysis target named target, you must in addition
# give the list of source files containing the code to be analyzed by adding
# them as dependencies of target.parse, a in
#
# target.parse: file1.c file2.c file3.c...
#

# Test if Makefile is > 4.0
ifneq (4.0,$(firstword $(sort $(MAKE_VERSION) 4.0)))
  $(error This Makefile requires Make >= 4.0 - available at http://ftp.gnu.org/gnu/make/)
endif


# --- Utilities ---

define display_command =
  $(info )
  $(info $(shell tput setaf 4)Command: $(1)$(shell tput sgr0))
  $(info )
endef

space :=
space +=
comma := ,

fc_list = $(subst $(space),$(comma),$(strip $1))


# --- Default configuration ---

FRAMAC     ?= frama-c
FRAMAC_GUI ?= frama-c-gui
SLEVEL     ?=
EVAFLAGS   ?= \
  -no-val-print -no-val-show-progress -value-msg-key=-initial-state \
  -val-print-callstacks -val-warn-copy-indeterminate @all -no-val-warn-on-alarms \
  -no-deps-print -no-calldeps-print \
  -memexec-all -inout-callwise -calldeps -permissive -from-verbose 0 \
  -val-builtins-auto \
  $(SLEVEL) \
  $(if $(EVABUILTINS), -val-builtin=$(call fc_list,$(EVABUILTINS)),) \
  $(if $(EVAUSESPECS), -val-use-spec $(call fc_list,$(EVAUSESPECS)),)
FCFLAGS    ?=
FCGUIFLAGS ?=

export LIBOVERLAY_SCROLLBAR=0


# --- Cleaning ---

.PHONY: clean
clean::
	$(RM) -r *.parse *.eva

clean-backups:
	find . -regextype posix-extended \
	  -regex '^.*_[0-9]{4}-[0-9]{2}-[0-9]{2}_[0-9]{2}-[0-9]{2}-[0-9]{2}\.eva(\.(log|stats|alarms|warnings|metrics))?' \
	  -delete


# --- Generic rules ---

TIMESTAMP    := $(shell date +"%Y-%m-%d_%H-%M-%S")
HR_TIMESTAMP := $(shell date +"%H:%M:%S %d/%m/%Y")# Human readable
DIR          := $(dir $(lastword $(MAKEFILE_LIST)))
SHELL        := /bin/bash
.SHELLFLAGS  := -eu -o pipefail -c

TIME_FORMAT  := user_time=%U\nmemory=%M

.ONESHELL:
.SECONDEXPANSION:
.FORCE:
.DELETE_ON_ERROR:

%.parse/command %.eva/command:
	@#

%.parse: SOURCES = $(filter-out %/command,$^)
%.parse: PARSE = $(FRAMAC) $(FCFLAGS) -cpp-extra-args="$(CPPFLAGS)" $(SOURCES)
%.parse: $$(if $$^,,.IMPOSSIBLE) $$(shell $(DIR)cmd-dep.sh $$*.parse/command $$(PARSE))
	@$(call display_command,$(PARSE))
	trap '$(RM) -r $@; printf "\nReceived SIGINT. Aborting.\n" ; exit 1' SIGINT
	mkdir --parent $@
	{
	  /usr/bin/time --format='$(TIME_FORMAT)' --output="$@/stats.txt" \
	    $(PARSE) \
	      -kernel-log w:$@/warnings.log \
	      -variadic-log w:$@/warnings.log \
	      -save $@/framac.sav \
	      -print -ocode $@/framac.ast -then -no-print \
	    || ($(RM) $@/stats.txt && false) # Prevents having error code reporting in stats.txt
	} 2>&1 |
	  tee $@/parse.log
	{
	  printf 'timestamp=%q\n' "$(HR_TIMESTAMP)";
	  printf 'warnings=%s\n' "`cat $@/warnings.log | grep ':\[kernel\]' | wc --lines`";
	  printf 'cmd_args=%q\n' "$(subst ",\",$(wordlist 2,999,$(PARSE)))"
	} >> $@/stats.txt
	touch $@ # Update timestamp and prevents remake if nothing changes

%.slevel.eva: SLEVEL = -slevel $(word 2,$(subst ., ,$*))
%.eva: EVA = $(FRAMAC) $(FCFLAGS) -val $(EVAFLAGS)
%.eva: PARSE_RESULT = $(word 1,$(subst ., ,$*)).parse
%.eva: $$(PARSE_RESULT) $$(shell $(DIR)cmd-dep.sh $$*.eva/command $$(EVA)) $(if $(BENCHMARK),.FORCE,)
	@$(call display_command,$(EVA))
	trap '$(RM) -r $@; printf "\nReceived SIGINT. Aborting.\n" ; exit 1' SIGINT
	mkdir --parent $@
	{
		/usr/bin/time --format='$(TIME_FORMAT)' --output="$@/stats.txt" \
	    $(EVA) \
	      -load $(PARSE_RESULT)/framac.sav -save $@/framac.sav \
	      -report-csv $@/alarms.csv -report-no-proven \
	      -kernel-log w:$@/warnings.log \
	      -from-log w:$@/warnings.log \
	      -inout-log w:$@/warnings.log \
	      -report-log w:$@/warnings.log \
	      -scope-log w:$@/warnings.log \
	      -value-log w:$@/warnings.log \
	      -metrics-log a:$@/metrics.log \
	      -metrics-value-cover \
	    || ($(RM) $@/stats.txt && false) # Prevents having error code reporting in stats.txt
	} 2>&1 |
	  sed --unbuffered '/\[value\] Values at end of function/,999999d' |
	  tee $@/eva.log
	$(DIR)parse-coverage.sh $@/eva.log $@/stats.txt
	{
	  printf 'timestamp=%q\n' "$(HR_TIMESTAMP)";
	  printf 'warnings=%s\n' "`cat $@/warnings.log | grep ':\[\(value\|kernel\|from\)\]' | wc --lines`";
	  printf 'alarms=%s\n' "`expr $$(cat $@/alarms.csv | wc --lines) - 1`";
	  printf 'cmd_args=%q\n' "$(subst ",\",$(wordlist 2,999,$(EVA)))"
	} >> $@/stats.txt
	touch $@ # Update timestamp and prevents remake if nothing changes
	cp -r $@ $*_$(TIMESTAMP).eva

%.gui: %
	$(FRAMAC_GUI) $(FCGUIFLAGS) -load $</framac.sav &

# Run loop bound analysis plug-in and store result in *.loop
%.loop: %
	@
	{
	  $(FRAMAC) $(FCFLAGS) -load $^/framac.sav -loop -loop-no-branches |
	    /bin/sed -e '1,/Add this to your command line:/d'
	} > $@


# clean is generally not the default goal, but if there is no default
# rule when including this file, it would be.

ifeq ($(.DEFAULT_GOAL),clean)
  .DEFAULT_GOAL :=
endif
