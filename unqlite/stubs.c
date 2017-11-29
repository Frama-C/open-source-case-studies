#ifdef __FRAMAC__
# include "__fc_builtin.h"
volatile int nondet;
extern int main(int, char **);
// main for EVA
int eva_main() {
  int argc = Frama_C_interval(0, 5);
  char argv0[256], argv1[256], argv2[256], argv3[256], argv4[256];
  char *argv[5] = {argv0, argv1, argv2, argv3, argv4};
  for (int i = 0; i < 5; i++) {
    for (int j = 0; j < 256; j++) {
      argv[i][j] = nondet;
    }
  }
  return main(argc, argv);
}
#endif // __FRAMAC__
