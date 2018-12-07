int main(int argc, char **argv);

#include "__fc_builtin.h"
volatile int nondet;
// main for EVA
int eva_main() {
  int argc = Frama_C_interval(0, 5);
  char argv0[256], argv1[256], argv2[256], argv3[256], argv4[256];
  char *argv[5] = {argv0, argv1, argv2, argv3, argv4};
  //@ loop unroll 5;
  for (int i = 0; i < 5; i++) {
    Frama_C_make_unknown(argv[i], 255);
    argv[i][255] = 0;
  }
  return main(argc, argv);
}
