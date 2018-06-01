TARGETS=2048 debie1-e-free gzip124 mini-gmp PapaBench-0.4 polarssl-1.1.7 \
     qlz solitaire tweetnacl-usable libmodbus monocypher khash \
     monocypher-0.6-tweaked jsmn chrony

help::
	@echo ""
	@echo "Known targets:"
	@echo "$(TARGETS)"

all: $(TARGETS)

$(TARGETS):
	+$(MAKE) -C $@

# use GNU parallel if available
PARALLEL := $(shell command -v parallel 2> /dev/null)

loop-all: $(TARGETS)
ifdef PARALLEL
	parallel $(MAKE) -C {} loop ::: $(TARGETS)
else
	$(foreach target,$(TARGETS),$(MAKE) -C $(target) loop ;)
endif

clean-all:
ifdef PARALLEL
	parallel $(MAKE) -C {} clean ::: $(TARGETS)
else
	$(foreach target,$(TARGETS),$(MAKE) -C $(target) clean ;)
endif

parse-all:
ifdef PARALLEL
	parallel $(MAKE) -C {} parse ::: $(TARGETS)
else
	$(foreach target,$(TARGETS),$(MAKE) -C $(target) parse ;)
endif

stats-all: $(TARGETS)
ifdef PARALLEL
	parallel $(MAKE) -s -C {} stats ::: $(TARGETS)
else
	$(foreach target,$(TARGETS),$(MAKE) -s -C $(target) stats ;)
endif

.PHONY: $(TARGETS) frama-c/build/bin/frama-c loop-all clean-all help stats-all
