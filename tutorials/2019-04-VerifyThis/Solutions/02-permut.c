/*@ requires a_valid: \valid(a);
    requires b_valid: \valid(b);
    assigns *a, *b;
    ensures a_value: *a == \at(*b,Pre);
    ensures b_value: *b == \at(*a, Pre);
*/
void swap(int* a, int *b);

/*@ requires a_valid: \valid(a);
    requires b_valid: \valid(b);
    requires c_valid: \valid(c);
    requires sep: \separated(a,b,c);
    ensures a_value: *a == \at(*b, Pre);
    ensures b_value: *b == \at(*c, Pre);
    ensures c_value: *c == \at(*a, Pre);
*/
void permut(int* a, int *b, int *c) {
  swap(a,b);
  swap(b,c);
}
