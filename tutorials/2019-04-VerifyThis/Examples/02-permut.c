/*@ requires a_valid: \valid(a);
    requires b_valid: \valid(b);
    ensures a_value: *a == \at(*b,Pre);
    ensures b_value: *b == \at(*a, Pre);
*/
void swap(int* a, int *b);

void permut(int* a, int *b, int *c) {
  swap(a,b);
  swap(b,c);
}
