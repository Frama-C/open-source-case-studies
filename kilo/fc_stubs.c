#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <sys/types.h>

#include "string.c" // for strdup
#include "stdio.c" // for getline

// Stub for getdelim
/*@
  requires valid_n: \valid(n);
  requires valid_lineptr: \valid(lineptr);
  requires valid_stream: \valid_read(stream); // will write to _some_ fields
  requires representable: delim != EOF;
  requires lineptr == \null || \valid(*lineptr+(0..*n-1)) && \freeable(*lineptr);
  assigns \result, *lineptr, (*lineptr)[0..], *n, *stream
     \from indirect:lineptr, indirect:n, indirect:delim,
        indirect:stream, indirect:*lineptr, indirect:*n, indirect:*stream,
        indirect:(*lineptr)[0..];
  ensures \result == -1 || \result >= 0;
 */
ssize_t getdelim(char **lineptr, size_t *n, int delim, FILE *stream);

// Size used for each chunk of memory allocated by getdelim()
#define __FC_GETDELIM_CHUNK_SIZE 128

ssize_t getdelim(char **lineptr, size_t *n, int delim, FILE *stream) {
  //@ assert \valid(lineptr);
  //@ assert \valid(n);
  //@ assert lineptr == \null && *n == 0 || \freeable(lineptr);
  if (*lineptr == NULL) {
    *lineptr = malloc(__FC_GETDELIM_CHUNK_SIZE);
    if (!*lineptr) /*TODO: errno = ENOMEM;*/ return -1;
    *n = __FC_GETDELIM_CHUNK_SIZE;
  }
  size_t i;
  char c;
  for (i = 0, c = getc(stream); c != EOF;) {
    if (i == *n) {
      if (SIZE_MAX - *n < __FC_GETDELIM_CHUNK_SIZE) {
        //TODO: errno = EOVERFLOW;
        return -1;
      }
      *lineptr = realloc(*lineptr, *n + __FC_GETDELIM_CHUNK_SIZE);
      if (!*lineptr) /*TODO: errno = ENOMEM;*/ return -1;
      *n += __FC_GETDELIM_CHUNK_SIZE;
    }
    (*lineptr)[i] = c;
    i++;
    if (c == delim) break;
    c = getc(stream);
  }
  // either found delim, or got EOF; in both cases, insert '\0' at the end,
  // allocating one extra byte if needed
  if (i == *n) {
    (*n)++;
    *lineptr = realloc(*lineptr, *n);
    if (*lineptr == NULL) /*TODO: errno = ENOMEM;*/ return -1;
  }
  (*lineptr)[i] = 0;
  return c == EOF && i == 0 ? -1 : i;
}

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
