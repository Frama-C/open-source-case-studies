#include <stddef.h>
#include <stdint.h>

/*@ predicate sorted{L}(int* a, integer low, integer high) =
  \forall integer i,j; low <= i <= j <= high ==> a[i] <= a[j];
*/

/*@
  logic integer count{L}(int *a, int key, integer low, integer high) =
    low > high ? 0 :
      (a[high] == key ?
        count(a,key,low,high - 1) + 1: count(a,key,low,high - 1));
*/

/*@ lemma count_id{L1,L2}:
  \forall int *a, key, integer low, high;
    (\forall integer i; low <= i <= high ==>
      \at(a[i],L1) == \at(a[i],L2)) ==>
      count{L1}(a,key,low, high) ==
      count{L2}(a,key,low, high);
*/

/*@ requires valid_block: \valid(a+(low .. high-1));
    requires ordered_bounds: low < middle < high;
    assigns \nothing;
    ensures count_split_eq:
     \forall int key;
      count(a,key,low,high-1) ==
        count(a,key,low,middle-1) + count(a,key,middle,high -1);
*/
void lemma_count_split(int* a, size_t low, size_t middle, size_t high) {
  /*@
   loop invariant middle <= i <= high;
   loop invariant
    \forall int key;
        count(a,key,low,i-1) ==
          count(a,key,low,middle-1) + count(a,key,middle,i-1);
      loop assigns i;
      loop variant high - i;
  */
  for (size_t i = middle; i < high; i++);
}

/*@ requires valid_a: \valid(a+(low_a .. low_a + length - 1));
    requires valid_b: \valid(b+(low_b .. low_b + length - 1));
    requires same_a_b:
      \forall integer i; 0 <= i < length ==> a[low_a+i] == b[low_b+i];
    assigns \nothing;
    ensures same_count:
      \forall int key;
        count(a,key,low_a,low_a+length - 1) ==
        count(b,key,low_b,low_b+length-1);
*/
void lemma_count_same(int *a, int* b,
                      size_t low_a, size_t low_b, size_t length) {
  /*@ loop invariant bounds: 0 <= i <= length;
      loop invariant same_count:
       \forall int key;
       count(a,key,low_a,low_a+i-1) == count(b,key,low_b,low_b+i-1);
       loop assigns i;
       loop variant length - i;
  */
  for(size_t i = 0; i < length; i++);
}

/*@
  requires slices: low < middle < high;
  requires array1: \valid(a + (low .. high - 1));
  requires sorted_low: sorted(a,low,middle - 1);
  requires sorted_high: sorted(a,middle, high - 1);
  assigns a[low .. high - 1];
  ensures sorted: sorted(a,low,high - 1);
  ensures count:
    \forall int key;
      count(a,key,low,high - 1) == count{Pre}(a,key,low,high - 1);
*/
void merge(int* a, size_t low, size_t middle, size_t high) {
  int tmp[SIZE_MAX];
  size_t lidx = low;
  size_t hidx = middle;
  /*@
    loop invariant idx: tidx == lidx + hidx - low - middle;
    loop invariant tidx_bound: 0 <= tidx <= high - low;
    loop invariant lidx_bound: low <= lidx <= middle;
    loop invariant hidx_bound: middle <= hidx <= high;
    loop invariant sorted: sorted(&tmp[0],0,tidx-1);
    loop invariant cmp_low: \forall integer i, j;
      0 <= i < tidx && lidx <= j < middle ==> tmp[i] <= a[j];
    loop invariant cmp_high: \forall integer i, j;
      0 <= i < tidx && hidx <= j < high ==> tmp[i] <= a[j];
    loop invariant count:
      \forall int key;
      count(&tmp[0],key,0,tidx-1) == count(a,key,low,lidx-1) + count(a,key,middle,hidx-1);
    loop assigns tidx, lidx, hidx, tmp[0 .. high - low - 1];
    loop variant high - tidx;
   */
  for (size_t tidx = 0; tidx < high - low; tidx++) {
    if (lidx >= middle) {
      //@ assert high_only: hidx < high;
      tmp[tidx] = a[hidx];
      hidx++;
    } else if (hidx >= high) {
      //@ assert low_only: lidx < middle;
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
  lemma_count_split(a,low,middle,high);
  /*@ assert tmp_all_elts:
      \forall int k; count(&tmp[0],k,0,high-low-1) == count(a,k,low,high-1);*/
  /*@
    loop invariant for_loop: 0 <= i <= high - low;
    loop invariant eq: \forall integer j; 0 <= j < i ==> a[low + j] == tmp[j];
    loop assigns i, a[low .. high - 1];
    loop variant high - i;
   */
  for (size_t i = 0; i < high - low; i++)
    a[low + i] = tmp[i];
  lemma_count_same(a,tmp,low,0,high-low);
}

/*@ requires valid_slice: \valid(a + (low .. high  - 1));
    decreases high - low; // not used by WP
    assigns a[low .. high - 1];
    ensures slice_sorted: sorted(a,low,high-1);
    ensures slice_all_elts:
      \forall int key;
        count{Here}(a,key,low,high-1) == count{Pre}(a,key,low, high -1 );
*/
void merge_sort_aux(int* a, size_t low, size_t high) {
  if (low < high) {
    size_t middle = low + (high - low) / 2;
    if (low < middle) {
      /*@ assert well_ordered: low < middle < high; */
      lemma_count_split(a,low,middle,high);
      merge_sort_aux(a,low,middle);
      lemma_count_split(a,low,middle,high);
      L: merge_sort_aux(a,middle,high);
      /*@
        assert helper_count: \forall int k;
          count(a,k,low,middle-1) == count{L}(a,k,low,middle-1); */
      lemma_count_split(a,low,middle,high);
      merge(a,low,middle,high);
    }
  }
}

/*@ requires valid_array: \valid(a + (0 .. length - 1));
    assigns a[0 .. length - 1];
    ensures sorted: sorted(a,0,length - 1);
    ensures all_elts:
      \forall int key;
        count{Here}(a,key,0,length-1) == count{Pre}(a,key,0,length -1 );
*/
void merge_sort(int* a, size_t length) { merge_sort_aux(a,0,length); }

/*
Local Variables:
compile-command: "frama-c -wp -wp-rte 06-mergesort.c -wp-session merge_sort_proofs -wp-script merge_sort_proofs/lemma_count_id.v -wp-prover script,alt-ergo,coq"
End:
*/
