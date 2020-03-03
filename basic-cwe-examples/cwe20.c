// Based on MITRE's CWE-20, demonstrative example 2
// https://cwe.mitre.org/data/definitions/20.html

#include <stdio.h>
#include <stdlib.h>

#define MAX_DIM 100

typedef struct _board_square_t {
  char color;
} board_square_t;

#define die(s) fprintf(stderr, s); exit(1)

int main() {

  /* board dimensions */
  int m,n, error;
  board_square_t *board;

  printf("Please specify the board height: \n");
  error = scanf("%d", &m);
  if ( EOF == error ){
    die("No integer passed: Die evil hacker!\n");
  }
  printf("Please specify the board width: \n");
  error = scanf("%d", &n);
  if ( EOF == error ){
    die("No integer passed: Die evil hacker!\n");
  }
  if ( m > MAX_DIM || n > MAX_DIM ) {
    die("Value too large: Die evil hacker!\n");
  }
  board = (board_square_t*) malloc( m * n * sizeof(board_square_t));

  return 0;
}
