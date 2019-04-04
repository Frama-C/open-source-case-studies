// sorts given array a of size length > 0
/*@
  axiomatic Count {
  logic integer count{L}(int* a, integer length, int c);
  axiom nil{L}: \forall int* a, c; count{L}(a,0,c) == 0;
  axiom is_here{L}: \forall int* a, c, integer l; l>0 && a[l-1] == c ==>
  count{L}(a,l,c) == count{L}(a,l-1,c) + 1;
  axiom is_absent{L}: \forall int* a, c, integer l; l>0 && a[l-1] !=c ==>
  count{L}(a,l,c) == count{L}(a,l-1,c);
}
*/

//@ lemma foo{L}: foo: \forall int* a, c, integer l,v; count{L}(a,l,c) == v;
 
/*@ requires \valid(a+(0 .. length - 1));
  requires length >= 0;
  assigns a[0..length-1];
  behavior sorted:
  ensures \forall integer i,j; 0<= i <=j < length ==> a[i] <= a[j];
  behavior same_elements:
  ensures 
  \forall int c; count(a,length,c) == count{Pre}(a,length,c);
 */
void sort (int* a, int length) {
  int current;
  /*@ loop invariant 0<=current<= length;
    loop assigns a[0..length-1], current;
    for sorted: loop invariant \forall integer i,j; 
    0<=i<=j<current ==>a[i]<=a[j];
    for sorted: loop invariant \forall integer i,j;
    0<=i<current<=j<length ==> a[i]<=a[j];
    for same_elements:
    loop invariant \forall int c; count(a,length,c) == count{Pre}(a,length,c);
    loop variant length - current;
  */
  for (current = 0; current < length - 1; current++) {
    int min_idx = current;
    int min = a[current];
    /*@
      loop invariant current+1<=i<=length;
      loop invariant current<=min_idx<i;
      loop invariant a[min_idx] == min;
      loop assigns min,min_idx,i;
      for sorted: loop invariant \forall integer j; current+1<=j<i ==> min <= a[j];
    */
    for (int i = current + 1; i < length; i++) {
      if (a[i] < min) {
	min = a[i];
	min_idx = i;
      }
    }
    if (min_idx != current){ 
      L: a[min_idx]=a[current];
      a[current]=0;
    }
  }  
}

/*
Local Variables:
compile-command: "frama-c-gui sort.c"
End:
*/
