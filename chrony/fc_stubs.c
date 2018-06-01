#include <string.h>
#include <stdlib.h>

volatile int qsort_nondet;
extern void qsort(void *base, size_t nmemb, size_t size,
                  int (*compar)(const void *, const void *)) {
  char *src = base, *dst = base;
  for (size_t dst_i = 0; dst_i < nmemb; dst_i++) {
    size_t src_i = qsort_nondet % nmemb * size;
    if (src_i != dst_i)
      memcpy(dst + (dst_i * size), src + src_i, size);
  }
}


int main(int argc, char **argv);
#include "__fc_builtin.h"
volatile int v;
void eva_main() {
  char argv0[50], argv1[50], argv2[50], argv3[50], argv4[50];
  char *argv[5] = {argv0, argv1, argv2, argv3, argv4};
  int argc = Frama_C_interval(0, 5);
  for (int i = 0; i < 5; i++) {
    for (int j = 0; j < 50; j++) {
      argv[i][j] = v;
    }
    argv[i][49] = 0; // force valid string
  }
  main(argc, argv);
}

#include <netdb.h>

static struct hostent h;

/*@
  requires valid_read_string(name);
*/
struct hostent *gethostbyname(const char *name) {
  h.h_name = "gethostbyname_name";
  h.h_aliases = 0;
  h.h_addrtype = AF_INET;
  h.h_length = sizeof(struct in_addr);
  h.h_addr_list = malloc(sizeof(char*));
  if (!h.h_addr_list) return 0;
  h.h_addr_list[0] = 0;
  return &h;
}
