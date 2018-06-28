#/bin/sh

exec frama-c -machdep x86_64 parser_full.c -val -slevel 10 -eva-symbolic-locations-domain \
 -then -wp -wp-prover alt-ergo,z3 -wp-timeout 1
