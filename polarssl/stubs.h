#include "include/polarssl/aes.h"
#include "include/polarssl/ssl.h"
#include "include/polarssl/timing.h"
#include "include/polarssl/x509.h"
#include "include/polarssl/sha1.h"
#include "include/polarssl/md5.h"
#include "include/polarssl/ctr_drbg.h"
#include "include/polarssl/camellia.h"
#include "include/polarssl/arc4.h"
#include "include/polarssl/des.h"

//@ghost volatile int _state;

/*@
  requires \valid(ctx);
  requires \valid_read(key + (0 .. 31));
  requires keysize == 128 || keysize == 192 || keysize == 256;
  assigns  ctx->nr \from keysize;
  assigns  ctx->rk, _state \from _state;
  ensures  \initialized(&ctx->rk);
  ensures  ctx->nr == 10 || ctx->nr == 12 || ctx->nr == 14;
 */
int aes_setkey_enc( aes_context *ctx, const unsigned char *key, unsigned int keysize );

/*@
  requires \valid(ctx);
  requires \valid_read(key + (0 .. 31));
  requires keysize == 128 || keysize == 192 || keysize == 256;
  assigns  ctx->nr \from keysize;
  assigns  ctx->rk, _state \from _state;
  ensures  \initialized(&ctx->rk);
  ensures  ctx->nr == 10 || ctx->nr == 12 || ctx->nr == 14;
 */
int aes_setkey_dec( aes_context *ctx, const unsigned char *key, unsigned int keysize );

/*@
  requires length % 16 == 0;
  requires \valid(iv + (0 .. 15));
  requires \valid(output+(0 .. length-1));
  requires \valid_read(input+(0 .. length-1));
  assigns  *(iv+(0 .. 15)) \from *(input+(0 .. length-1));
  assigns  *(output+(0 .. length-1)) \from *(input+(0 .. length-1)), *(iv+(0 .. 15));
  assigns  \result \from _state;
 */
int aes_crypt_cbc( aes_context *ctx,
                    int mode,
                    size_t length,
                    unsigned char iv[16],
                    const unsigned char *input,
		   unsigned char *output );

/*@ assigns \nothing;
*/
void x509_free( x509_cert *crt );

/*@
  assigns \result \from \nothing;
*/
int x509parse_crt( x509_cert *chain, const unsigned char *buf, size_t buflen );

//@ ghost volatile int _rsa_keyfile;
/*@ 
  requires \valid(rsa);
  assigns \result  \from _rsa_keyfile;
  assigns rsa->N   \from _rsa_keyfile;
  assigns rsa->E   \from _rsa_keyfile;
  assigns rsa->D   \from _rsa_keyfile;
  assigns rsa->P   \from _rsa_keyfile;
  assigns rsa->Q   \from _rsa_keyfile;
  assigns rsa->DP  \from _rsa_keyfile;
  assigns rsa->DQ  \from _rsa_keyfile;
  assigns rsa->QP  \from _rsa_keyfile;
  assigns rsa->len \from _rsa_keyfile;
*/
int x509parse_key( rsa_context *rsa, const unsigned char *key, size_t keylen,
		   const unsigned char *pwd, size_t pwdlen );

//@ ghost volatile long _hardclock_clock;
/*@
  assigns \result \from _hardclock_clock;
 */
unsigned long hardclock(void);

/*@
  requires \valid(ctx);
  requires \valid(ctx->state + (0 .. 4));
  requires \initialized(ctx->state + (0 .. 4));
  requires \valid_read(data + (0 .. 63));
  assigns *(ctx->state + (0 .. 4)) \from _state;
  ensures \initialized(ctx->state + (0 .. 4));
 */
void sha1_process( sha1_context *ctx, const unsigned char data[64] );

/*@
  requires \valid(ctx);
  requires \initialized(ctx->total + (0 .. 1));
  requires \initialized(ctx->state + (0 .. 4));

  assigns *(ctx->total + (0 .. 1)) \from _state;
  assigns *(ctx->state + (0 .. 4)) \from _state;
  assigns *(ctx->buffer + (0 .. 63)) \from _state;
  assigns *(ctx->ipad + (0 .. 62)) \from _state;
  assigns *(output + (0 .. 19)) \from _state;
  ensures \initialized(output + (0 .. 19));
 */
void sha1_finish( sha1_context *ctx, unsigned char output[20] );

/*@
  requires \valid_read(input + (0 .. ilen-1));
  requires \initialized(input + (0 .. ilen-1));
  requires \valid(output + (0 .. 63));
  assigns *(output + (0 .. 63)) \from *(input + (0 .. ilen-1)), ilen;
  ensures \initialized(output + (0 .. 63));
*/
void sha4( const unsigned char *input, size_t ilen,
	     unsigned char output[64], int is384 );

/*@
  requires \valid(ctx);
  requires \valid_read(input + (0 .. 15));
  requires \valid(output + (0 .. 15));
  assigns  \result \from _state;
  assigns  *(output + (0 .. 15)) \from _state;
  ensures  \initialized(output + (0 .. 15));
 */
int aes_crypt_ecb( aes_context *ctx, int mode, const unsigned char input[16], unsigned char output[16] );

/*@
  requires \valid(ctx);
  requires \valid_read(data + (0 .. 63));
  assigns *(ctx->state + (0 .. 3)) \from _state;
  ensures \initialized(ctx->state + (0 .. 3));
 */
void md5_process( md5_context *ctx, const unsigned char data[64] );

/*@
  requires \valid(output + (0 .. 15));
 */
void md5( const unsigned char *input, size_t ilen, unsigned char output[16] );

/*@ requires \valid(output+(0..15)); */
void md5_finish( md5_context *ctx, unsigned char output[16] );

//@ghost volatile int _ctr_drbg_random_source;
/*@
  requires \valid((ctr_drbg_context*)p_rng);
  requires \valid(output + (0 .. output_len - 1));
  assigns *(output + (0 .. output_len - 1)), _ctr_drbg_random_source \from _ctr_drbg_random_source;
  assigns \result \from _ctr_drbg_random_source;
  ensures \initialized(output + (0 .. output_len - 1));
 */
int ctr_drbg_random( void *p_rng, unsigned char *output, size_t output_len );


/*@
  requires \valid(ctx);
  requires \valid(olen);
  assigns \result, _state \from _state;
  assigns *olen \from _state;
  assigns ctx->len \from _state;
  assigns ctx->X \from _state;
  assigns ctx->P \from _state;
  assigns ctx->G \from _state;
  assigns ctx->GX \from _state;
  ensures \initialized(&ctx->len);
  ensures \initialized(olen);
  ensures ctx->len == 128; // actual value during execution
 */
int dhm_make_params( dhm_context *ctx, int x_size,
                     unsigned char *output, size_t *olen,
                     int (*f_rng)(void *, unsigned char *, size_t),
		       void *p_rng );

/*@
  requires \valid(X);
  requires \valid_read(A);
  requires \valid_read(E);
  requires \valid_read(N);
  assigns  \result, _state \from _state;
  assigns  *X \from _state;
  ensures X->s == 1 || X->s == -1;
 */
int mpi_exp_mod( mpi *X, const mpi *A, const mpi *E, const mpi *N, mpi *_RR );

/*@
  requires \valid_read(X);
  assigns \result, _state \from _state;
 */
size_t mpi_size( const mpi *X );

/*@
  assigns  *X \from _state;
 */
void mpi_free( mpi *X );

/*@
  requires \valid_read(X);
  assigns \result, _state \from _state;
 */
size_t mpi_msb( const mpi *X );

/*@
  requires \valid_read(X);
  assigns \result, *(buf + (0 .. buflen-1)), _state \from _state;
  ensures \initialized(buf + (0 .. buflen-1));
 */
int mpi_write_binary( const mpi *X, unsigned char *buf, size_t buflen );

/*@
  requires \valid_read(X);
  requires \valid_read(Y);
  assigns \result, _state \from _state;
 */
int mpi_cmp_mpi( const mpi *X, const mpi *Y );

/*@
  requires \valid_read(X);
  requires \valid_read(Y);
  assigns \result, _state \from _state;
 */
int mpi_cmp_abs( const mpi *X, const mpi *Y );

/*@
  requires \valid(X);
  requires \valid_read(Y);
  assigns *X, \result, _state \from _state;
  ensures X->s == 1 || X->s == -1;
 */
int mpi_copy( mpi *X, const mpi *Y );

/*@
  requires \valid(X);
  requires \valid_read(A);
  requires \valid_read(B);
  assigns *X, \result, _state \from _state;
  ensures X->s == 1 || X->s == -1;
 */
int mpi_sub_mpi( mpi *X, const mpi *A, const mpi *B );

/*@
  requires \valid(X);
  requires \valid_read(A);
  requires \valid_read(B);
  assigns *X, \result, _state \from _state;
  ensures X->s == 1 || X->s == -1;
 */
int mpi_mul_mpi( mpi *X, const mpi *A, const mpi *B );

/*@
  requires \valid(R);
  requires \valid_read(A);
  requires \valid_read(B);
  assigns *R, \result, _state \from _state;
  ensures R->s == 1 || R->s == -1;
 */
int mpi_mod_mpi( mpi *R, const mpi *A, const mpi *B );

/*@
  requires \valid(X);
  requires \valid_read(A);
  requires \valid_read(B);
  assigns *X, \result, _state \from _state;
  ensures X->s == 1 || X->s == -1;
 */
int mpi_add_abs( mpi *X, const mpi *A, const mpi *B );

/*@
  requires \valid(X);
  requires \valid_read(A);
  requires \valid_read(B);
  assigns *X, \result, _state \from _state;
  ensures X->s == 1 || X->s == -1;
 */
int mpi_sub_abs( mpi *X, const mpi *A, const mpi *B );

/*@
  requires \valid(X);
  assigns  \result, *X, _state \from _state;
  ensures \result == 0 || \result == POLARSSL_ERR_MPI_MALLOC_FAILED;
  ensures X->s == 1 || X->s == -1;
 */
int mpi_fill_random( mpi *X, size_t size,
                     int (*f_rng)(void *, unsigned char *, size_t),
                     void *p_rng );

/*@
  requires \valid_read(s);
  requires \valid(X);
  assigns \result, *X, _state \from _state;
  ensures X->s == 1 || X->s == -1;
 */
int mpi_read_string( mpi *X, int radix, const char *s );

/*@
  requires \valid_read(buf + (0 .. buflen-1));
  requires \valid(X);
  assigns \result, *X, _state \from _state;
  ensures X->s == 1 || X->s == -1;
 */
int mpi_read_binary( mpi *X, const unsigned char *buf, size_t buflen );

/*@
  requires \valid(ctx);
  requires \valid_read(input + (0 .. length-1));
  requires \valid(output + (0 .. length-1));
  assigns *(output + (0 .. length-1)), _state \from _state;
  ensures \initialized(output + (0 .. length-1));
*/
int arc4_crypt( arc4_context *ctx, size_t length, const unsigned char *input,
		  unsigned char *output );

/*@
  assigns \nothing;
 */
void ssl_free(ssl_context *ssl);

/*@
  requires length % 16 == 0;
  requires \valid(iv + (0 .. 15));
  requires \valid(output+(0 .. length-1));
  requires \valid_read(input+(0 .. length-1));
  assigns  *(iv+(0 .. 15)) \from *(input+(0 .. length-1));
  assigns  *(output+(0 .. length-1)) \from *(input+(0 .. length-1)), *(iv+(0 .. 15));
  assigns  \result \from _state;
 */
int camellia_crypt_cbc( camellia_context *ctx,
                    int mode,
                    size_t length,
                    unsigned char iv[16],
                    const unsigned char *input,
			  unsigned char *output );

/*@
  requires \valid(ctx);
  requires \initialized(input + (0 .. 7));
  assigns \result, _state \from _state;
  assigns *(output + (0 .. 7)) \from *(input + (0 .. 7));
  ensures \initialized(output + (0.. 7));
 */
int des3_crypt_ecb( des3_context *ctx,
                     const unsigned char input[8],
		    unsigned char output[8] );

/*@
  assigns *(output + (0 .. length-1)) \from *(output + (0 .. length-1)), *(iv + (0 .. 7));
  assigns *(iv + (0 .. 7)) \from *(output + (0 .. length-1)), *(iv + (0 .. 7));
  assigns \result \from length;
  behavior invalid_length:
    assumes length % 8 != 0;
    assigns \result \from length;
    ensures \result == POLARSSL_ERR_DES_INVALID_INPUT_LENGTH;
  behavior des3_cbc_ok:
    assumes length % 8 == 0;
    requires \valid(ctx);
    requires \valid_read(input + (0 .. length-1));
    requires \initialized(input + (0 .. length-1));
    requires \initialized(iv + (0 .. 7));
    assigns *(output + (0 .. length-1)) \from *(output + (0 .. length-1)), *(iv + (0 .. 7));
    assigns *(iv + (0 .. 7)) \from *(output + (0 .. length-1)), *(iv + (0 .. 7));
    assigns \result \from length;
    ensures \initialized(output + (0 .. length-1));
    ensures \result == 0;
  disjoint behaviors;
  complete behaviors;
 */
int des3_crypt_cbc( des3_context *ctx,
                     int mode,
                     size_t length,
                     unsigned char iv[8],
                     const unsigned char *input,
                     unsigned char *output );

//@ ghost volatile int __fc_recv_status;
/*@
  requires \valid(buf+(0 .. len-1));
  requires \valid((int *)ctx);
  assigns *(buf+(0 .. len-1)), \result \from *((int *)ctx), len, __fc_recv_status;
  behavior error:
    assumes __fc_recv_status < 0;
    assigns \result \from __fc_recv_status;
    ensures \result < 0;
  behavior ok:
    assumes __fc_recv_status >= 0;
    assigns *(buf+(0 .. len-1)), \result \from *((int *)ctx), len, __fc_recv_status;
    ensures 0 <= \result <= len;
  complete behaviors;
  disjoint behaviors;
 */
int fc_recv( void *ctx, unsigned char *buf, size_t len );

#include "include/polarssl/sha4.h"
/*@
  requires \valid_read(input + (0 .. ilen-1));
  requires \valid(ctx->state + (0 .. 7));
  requires \valid(ctx->total + (0 .. 1));
  requires \valid(ctx->buffer + (0 .. 127));
  assigns ctx->state[0 .. 7] \from ctx->state[0 .. 7], input[0 .. 127],
                                   indirect:ilen;
  assigns ctx->total[0 .. 1] \from ctx->total[0 .. 1], ilen;
  assigns ctx->buffer[0 .. 127] \from input[0 .. 127], indirect:ilen;
 */
void sha4_update( sha4_context *ctx, const unsigned char *input, size_t ilen );
