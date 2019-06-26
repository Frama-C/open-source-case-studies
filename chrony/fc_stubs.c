#include <string.h>
#include <stdlib.h>

// Simulates a non-deterministic sorting (or, more precisely, shuffling)
// function, used to detect runtime errors only.
volatile int qsort_nondet;
extern void qsort(void *base, size_t nmemb, size_t size,
                  int (*compar)(const void *, const void *)) {
  char *src = base, *dst = base;
  for (size_t dst_i = 0; dst_i < nmemb; dst_i++) {
    size_t src_i = qsort_nondet % nmemb;
    if (src_i != dst_i)
      memcpy(dst + (dst_i * size), src + (src_i * size), size);
  }
}

// Sets up the initial context, with up to 5 arguments containing
// random strings of up to 50 characters each
int main(int argc, char **argv);
#include "__fc_builtin.h"
volatile int v;
void eva_main() {
  char argv0[50], argv1[50], argv2[50], argv3[50], argv4[50];
  char *argv[5] = {argv0, argv1, argv2, argv3, argv4};
  int argc = Frama_C_interval(0, 5);
  //@ loop unroll 5;
  for (int i = 0; i < 5; i++) {
    Frama_C_make_unknown(argv[i], 49);
    argv[i][49] = 0; // force valid string
  }
  main(argc, argv);
}
