// Based on MITRE's CWE-190, demonstrative example 2
// https://cwe.mitre.org/data/definitions/190.html

// By default, Frama-C/Eva does not report unsigned overflows as alarms;
// nevertheless, in the code below, Eva reports an alarm when trying to
// write to the (under-allocated) buffer.
// Adding option "-warn-unsigned-overflow" ensures Eva reports the
// overflow as soon as it happens.
// Also, adding option "-eva-no-alloc-returns-null" allows focusing on this
// issue while ignoring the the fact that malloc() may fail (which would
// require an extra check).

#include <stdlib.h>

int packet_get_int_ok() {
  return 123456;
}

int packet_get_int_problem() {
  return 1073741824;
}

char *packet_get_string(const char *s) {
  return "string";
}

int main() {
  char **response;
  int nresp = packet_get_int_ok();
  if (nresp > 0) {
    response = malloc(nresp*sizeof(char*));
    for (int i = 0; i < nresp; i++) response[i] = packet_get_string(NULL);
  }
  free(response);

  nresp = packet_get_int_problem();
  if (nresp > 0) {
    response = malloc(nresp*sizeof(char*));
    for (int i = 0; i < nresp; i++) response[i] = packet_get_string(NULL);
  }
  free(response);
  return 0;
}
