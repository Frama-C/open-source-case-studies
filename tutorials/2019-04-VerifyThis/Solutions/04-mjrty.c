/*@ logic integer count(unsigned* a, integer length, unsigned cand) =
  length == 0 ? 0 :
    a[length - 1] == cand
     ? count(a,length - 1,cand) + 1
     : count(a,length-1,cand);
*/

/*@ predicate majority(unsigned *a, unsigned length, unsigned cand) =
  count(a,length,cand)>length/2;
*/

// should be ghost
/*@ requires \valid(a + (0 .. length2-1));
    requires 0<= length1 <= length2;
    assigns \nothing;
    ensures count(a,length1,elt) <= count(a,length2,elt);
*/
void lemma_func_count_subset(
  unsigned*a, unsigned length1, unsigned length2, unsigned elt) {
  /*@ loop invariant length1 <= i <= length2;
      loop invariant count(a,length1,elt) <= count(a,i,elt);
      loop assigns i;
  */
  for (unsigned int i = length1; i<length2; i++) { }
}

/*@ predicate wf_result(unsigned*a, unsigned length) =
  \forall integer i; 0<=i<length ==> 0< a[i]; */

/*@ requires length > 0;
    requires \valid(a+(0 .. length - 1));
    requires wf_result(a,length);
    assigns \nothing;
    behavior has_majority:
    assumes \exists unsigned cand; 
      majority(a,length,cand);
    ensures majority(a,length,\result);
    behavior no_majority:
    assumes \forall unsigned cand; 
      !majority(a,length,cand);
    ensures \result == 0;
    complete behaviors;
    disjoint behaviors;
*/
unsigned mjrty(unsigned* a, unsigned length) {
  unsigned cand = a[0];
  unsigned cnt = 1;
  /*@ loop invariant 1<= i <= length;
      loop invariant cnt <= count(a,i,cand);
      loop invariant \forall unsigned c; c!=cand ==> 
        0 <= 2*count(a,i,c) <= i-cnt;
      loop invariant 2*(count(a,i,cand) - cnt) <= i-cnt;
      loop assigns i,cnt,cand;
      loop variant length - i;
   */
  for(unsigned i=1; i<length; i++) {
    if (cnt == 0) {
      cand = a[i];
      cnt = 1;
      //@ assert count(a,i+1,cand)>=1;
    } else {
      if (a[i] == cand) cnt++;
      else cnt--;
    }
    if (cnt>length/2) {
      /*@ ghost lemma_func_count_subset(a,i+1,length,cand); */
      /*@ assert majority(a,length,cand); */ return cand;
    }
  }
  /*@ assert \forall unsigned c; c!=cand ==> !majority(a,length,c); */
  cnt = 0;
  /*@ loop invariant 0<=i<=length;
      loop invariant cnt == count(a,i,cand);
      loop invariant cnt<=length/2;
      loop assigns i,cnt;
      loop variant length - i;
   */
  for (unsigned i=0; i<length; i++) {
    if (a[i] == cand) cnt++;
    if (cnt>length/2) {
      /*@ ghost lemma_func_count_subset(a,i+1,length,cand); */
      /*@ assert majority(a,length,cand); */
      return cand; }
  }
  return 0;
}
