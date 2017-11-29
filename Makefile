TARGETS=2048 debie1-e-free gzip124 mini-gmp PapaBench-0.4 polarssl-1.1.7 \
     qlz solitaire tweetnacl-usable unqlite libmodbus monocypher khash \
     monocypher-0.6-tweaked jsmn

help::
	@echo ""
	@echo "Known targets:"
	@echo "$(TARGETS)"

all: $(TARGETS)

$(TARGETS):
	+$(MAKE) -C $@

loop: $(TARGETS)
	$(foreach target,$(TARGETS),$(MAKE) -C $(target) loop ;)

clean-all:
	$(foreach target,$(TARGETS),$(MAKE) -C $(target) clean ;)

parse-all:
	$(foreach target,$(TARGETS),$(MAKE) -C $(target) parse ;)

stats:
	$(foreach target,$(TARGETS),$(MAKE) -s -C $(target) stats ;)

.PHONY: $(TARGETS) clean-all help stats
