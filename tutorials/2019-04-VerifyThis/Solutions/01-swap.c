/*@ requires a_valid: \valid(a);
    requires b_valid: \valid(b);
    ensures a_value: *a == \at(*b, Pre);
    ensures b_value: *b == \at(*a, Pre);
*/
void swap(int* a, int* b) {
  int tmp = *a;
  *a = *b;
  *b = tmp;
}
