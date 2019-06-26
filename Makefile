TARGETS=2048 debie1 gzip124 mini-gmp papabench polarssl \
     qlz solitaire tweetnacl-usable libmodbus monocypher khash \
     jsmn chrony hiredis semver kilo icpc cerberus itc-benchmarks

help::
	@echo ""
	@echo "Known targets:"
	@echo "$(sort $(TARGETS))"

QUICK_TARGETS=$(filter-out polarssl gzip124 monocypher chrony,$(TARGETS))

all: $(TARGETS)

$(TARGETS):
	+$(MAKE) -C $@

quick: $(QUICK_TARGETS)

%.loop:
	$(MAKE) -C $* loop

loop-all: $(addsuffix .loop,$(TARGETS))

%.clean:
	$(MAKE) -C $* clean

clean-all: $(addsuffix .clean,$(TARGETS))

%.parse:
	$(MAKE) -C $* parse

parse-all: $(addsuffix .parse,$(TARGETS))

%.stats:
	$(MAKE) -C $* stats

stats-all: $(addsuffix .stats,$(TARGETS))

display-targets:
	@echo $(foreach target,$(TARGETS),\
	        $(addprefix $(target)/,\
	          $(shell $(MAKE) --quiet -C $(target) display-targets)))

.PHONY: $(TARGETS) frama-c/build/bin/frama-c loop-all clean-all help stats-all
