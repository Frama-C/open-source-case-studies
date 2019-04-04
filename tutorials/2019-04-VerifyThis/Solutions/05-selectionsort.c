/*@ predicate sorted{L}(int* a, integer length) =
      \forall integer i,j; 0<=i<=j<length ==> a[i]<=a[j]; 
*/
/*@ predicate swap{L1,L2}(int* a,integer i,integer j,integer length)=
      0<=i<j<length 
      && \at(a[i],L1) == \at(a[j],L2)
      && \at(a[i],L2) == \at(a[j],L1)
      && \forall integer k; 0<=k<length && k!=i && k!=j ==>
           \at(a[k],L1) == \at(a[k],L2); 
*/
/*@ inductive same_elements{L1,L2}(int*a , integer length) {
      case refl{L}: 
        \forall int*a, integer length; same_elements{L,L}(a,length);
      case swap{L1,L2}: \forall int*a, integer i,j,length;
        swap{L1,L2}(a,i,j,length) ==> same_elements{L1,L2}(a,length);
      case trans{L1,L2,L3}: \forall int*a, integer length;
        same_elements{L1,L2}(a,length)
	==> same_elements{L2,L3}(a,length)
	==> same_elements{L1,L3}(a,length);
}
*/
/*@ requires \valid(a+(0..length-1));
    requires length > 0;
    assigns a[0..length-1];
    behavior sorted:
      ensures sorted(a,length);
    behavior same_elements:
      ensures same_elements{Pre,Here}(a,length);
*/
void sort (int* a, int length) {
  int current;
  /*@ loop invariant 0<=current<length;
      loop assigns a[0..length-1],current;
      for sorted: loop invariant sorted(a,current);
      for sorted: loop invariant
        \forall integer i,j; 0<=i<current<=j<length ==> a[i] <= a[j];
      for same_elements: loop invariant
        same_elements{Pre,Here}(a,length);
      loop variant length-current;
   */
  for (current = 0; current < length - 1; current++) {
    int min_idx = current;
    int min = a[current];
    /*@ loop invariant current+1<=i<=length;
        loop assigns i,min,min_idx;
        loop invariant current<=min_idx<i;
        loop invariant a[min_idx] == min;
        for sorted: loop invariant
          \forall integer j; current<=j<i ==> min <= a[j];
        loop variant length -i;
    */
    for (int i = current + 1; i < length; i++) {
      if (a[i] < min) {
	min = a[i];
	min_idx = i;
      }
    }
    if(min_idx != current) {
       L: a[min_idx]=a[current];
       a[current]=min;
/*@for same_elements:assert swap{L,Here}(a,current,min_idx,length);*/
    }
  }
}
