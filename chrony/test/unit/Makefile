TEST_WRAPPER =
CHRONY_SRCDIR = ../..

CC = gcc
CFLAGS = -O2 -g -D_FORTIFY_SOURCE=2 -fPIE -fstack-protector-strong --param=ssp-buffer-size=4 -Wmissing-prototypes -Wall
CPPFLAGS = -I$(CHRONY_SRCDIR) -nostdlib
LDFLAGS =  -pie -Wl,-z,relro,-z,now -lm  -lrt

SHARED_OBJS = test.o

TEST_OBJS := $(sort $(patsubst %.c,%.o,$(wildcard *.c)))
TESTS := $(patsubst %.o,%.test,$(filter-out $(SHARED_OBJS),$(TEST_OBJS)))

FILTER_OBJS = %/main.o %/client.o %/getdate.o
CHRONY_OBJS := $(filter-out $(FILTER_OBJS),$(wildcard $(CHRONY_SRCDIR)/*.o))

all: $(TESTS)

%.test: %.o $(SHARED_OBJS)
	$(CC) $(CFLAGS) -o $@ $^ $(CHRONY_OBJS:%/$*.o=) $(LDFLAGS)

%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $<

check: $(TESTS)
	@ret=0; \
	for t in $^; do \
	  $(TEST_WRAPPER) ./$$t || ret=1; \
	done; \
	exit $$ret

clean:
	rm -f *.o $(TESTS)
	rm -rf .deps

distclean: clean
	rm -f Makefile

.deps:
	@mkdir .deps

.deps/%.d: %.c | .deps
	@$(CC) -MM $(CPPFLAGS) -MT '$(<:%.c=%.o) $@' $< -o $@

-include $(TEST_OBJS:%.o=.deps/%.d)
