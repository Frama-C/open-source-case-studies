#include "stddef.h"

size_t binary_search(char* a, size_t length, char key) {
  size_t low = 0;
  size_t high = length - 1;
  while (high >= low) {
    size_t middle = (high + low) / 2;
    if (a[middle] == key) return middle;
    if (a[middle] < key) low = middle + 1;
    else high = middle - 1;
  }
  return length;
}
