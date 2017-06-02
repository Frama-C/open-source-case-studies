#include <stdint.h>
#include <stdlib.h>

/*@
  requires \valid(strp);
  assigns \result, *strp \from fmt;
  ensures \initialized(strp);
  allocates strp;
*/
int asprintf(char **strp, const char *fmt, ...);

/*@
  requires \valid(strp);
  assigns \result, *strp \from fmt;
  ensures \initialized(strp);
  allocates strp;
*/
int __gmp_asprintf(char **strp, const char *fmt, ...);

#include "gmp.h"
/*@
  assigns *a, __fc_random_counter \from __fc_random_counter;
*/
void __gmpz_init(mpz_ptr a);

/*@
  assigns *a, *b, __fc_random_counter \from __fc_random_counter;
*/
void __gmpz_rrandomb(mpz_ptr a, __gmp_randstate_struct * b, mp_bitcnt_t c);

/*@
  assigns \result, *a, __fc_random_counter \from __fc_random_counter;
*/
unsigned long __gmp_urandomb_ui(__gmp_randstate_struct *a, unsigned long b);

/*@
  requires \valid(res);
  assigns *res \from a, b;
  ensures \initialized(res);
*/
void __gmpz_add(mpz_ptr res, mpz_srcptr a, mpz_srcptr b);

/*@
  assigns *a, __fc_random_counter \from __fc_random_counter;
*/
void __gmpz_clear(mpz_ptr a);

/*@
  assigns *res \from a, b;
*/
void __gmpz_sub(mpz_ptr res, mpz_srcptr a, mpz_srcptr b);

/*@
  assigns *res \from a, b;
*/
void __gmpz_mul(mpz_ptr res, mpz_srcptr a, mpz_srcptr b);

/*@
  assigns *res \from a, b;
*/
void __gmpz_and(mpz_ptr res, mpz_srcptr a, mpz_srcptr b);

/*@
  assigns *res \from a, b;
*/
void __gmpz_ior(mpz_ptr res, mpz_srcptr a, mpz_srcptr b);

/*@
  assigns *res \from a, b;
*/
void __gmpz_xor(mpz_ptr res, mpz_srcptr a, mpz_srcptr b);

/*@
  assigns *res \from a, b;
*/
void __gmpz_lcm(mpz_ptr res, mpz_srcptr a, mpz_srcptr b);

/*@
  assigns *res \from a, b;
*/
void __gmpz_gcd(mpz_ptr res, mpz_srcptr a, mpz_srcptr b);
