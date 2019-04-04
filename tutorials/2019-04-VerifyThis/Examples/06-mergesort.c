#include <stddef.h>
#include <stdint.h>

void merge(int* a, size_t low, size_t middle, size_t high) {
  int tmp[SIZE_MAX];
  size_t lidx = low;
  size_t hidx = middle;
  for (size_t tidx = 0; tidx < high - low; tidx++) {
    if (lidx >= middle) {
      tmp[tidx] = a[hidx];
      hidx++;
    } else if (hidx >= high) {
      tmp[tidx] = a[lidx];
      lidx++;
    } else if (a[lidx] <= a[hidx]) {
      tmp[tidx] = a[lidx];
      lidx++;
    } else {
      tmp[tidx] = a[hidx];
      hidx++;
    }
  }
  for (size_t i = 0; i < high - low; i++)
    a[low + i] = tmp[i];
  lemma_count_same(a,tmp,low,0,high-low);
}

void merge_sort_aux(int* a, size_t low, size_t high) {
  if (low < high) {
    size_t middle = low + (high - low) / 2;
    if (low < middle) {
      lemma_count_split(a,low,middle,high);
      merge_sort_aux(a,low,middle);
      lemma_count_split(a,low,middle,high);
      merge_sort_aux(a,middle,high);
      lemma_count_split(a,low,middle,high);
      merge(a,low,middle,high);
    }
  }
}

void merge_sort(int* a, size_t length) { merge_sort_aux(a,0,length); }
