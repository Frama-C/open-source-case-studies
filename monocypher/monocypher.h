#ifndef MONOCYPHER_H
#define MONOCYPHER_H

#include <inttypes.h>
#include <stddef.h>

// Constant time equality verification
// returns 0 if it matches, something else otherwise.
int crypto_memcmp(const uint8_t *p1, const uint8_t *p2, size_t n);

////////////////
/// Chacha20 ///
////////////////
typedef struct {
    uint32_t input[16];       // current input, unencrypted
    uint8_t  random_pool[64]; // last input, encrypted
    uint8_t  pool_index;      // pointer to random_pool
} crypto_chacha_ctx;

void crypto_chacha20_H(uint8_t       out[32],
                       const uint8_t key[32],
                       const uint8_t in [16]);

void crypto_chacha20_init(crypto_chacha_ctx *ctx,
                          const uint8_t      key[32],
                          const uint8_t      nonce[8]);

void crypto_chacha20_Xinit(crypto_chacha_ctx *ctx,
                           const uint8_t      key[32],
                           const uint8_t      nonce[24]);

void crypto_chacha20_encrypt(crypto_chacha_ctx *ctx,
                             const uint8_t     *plain_text,
                             uint8_t           *cipher_text,
                             size_t             message_size);

void crypto_chacha20_random(crypto_chacha_ctx *ctx,
                            uint8_t           *cipher_text,
                            size_t             message_size);

/////////////////
/// Poly 1305 ///
/////////////////
typedef struct {
    uint32_t r[4];
    uint32_t h[5];
    uint32_t c[5];
    uint32_t pad[5];
    size_t   c_index;
} crypto_poly1305_ctx;

void crypto_poly1305_init(crypto_poly1305_ctx *ctx, const uint8_t key[32]);

void crypto_poly1305_update(crypto_poly1305_ctx *ctx,
                            const uint8_t *m, size_t bytes);

void crypto_poly1305_finish(crypto_poly1305_ctx *ctx, uint8_t mac[16]);

void crypto_poly1305_auth(uint8_t        mac[16],
                          const uint8_t *msg, size_t msg_length,
                          const uint8_t  key[32]);

////////////////
/// Blake2 b ///
////////////////
typedef struct {
    uint8_t  buf[128];      // input buffer
    uint64_t hash[8];       // chained state
    uint64_t input_size[2]; // total number of bytes
    uint8_t  c;             // pointer for buf[]
    uint8_t  output_size;   // digest size
} crypto_blake2b_ctx;

void crypto_blake2b_general_init(crypto_blake2b_ctx *ctx, size_t outlen,
                                 const uint8_t      *key, size_t keylen);

void crypto_blake2b_init(crypto_blake2b_ctx *ctx);

void crypto_blake2b_update(crypto_blake2b_ctx *ctx,
                           const uint8_t *in, size_t inlen);

void crypto_blake2b_final(crypto_blake2b_ctx *ctx, uint8_t *out);

void crypto_blake2b_general(uint8_t       *out, size_t outlen, // digest
                            const uint8_t *key, size_t keylen, // optional secret
                            const uint8_t *in , size_t inlen);

void crypto_blake2b(uint8_t out[64], const uint8_t *in, size_t inlen);

////////////////
/// Argon2 i ///
////////////////
void crypto_argon2i(uint8_t       *tag,       uint32_t tag_size,      // >= 4
                    const uint8_t *password,  uint32_t password_size,
                    const uint8_t *salt,      uint32_t salt_size,     // >= 8
                    const uint8_t *key,       uint32_t key_size,
                    const uint8_t *ad,        uint32_t ad_size,
                    void    *work_area,
                    uint32_t nb_blocks,                               // >= 8
                    uint32_t nb_iterations);

///////////////
/// X-25519 ///
///////////////
void crypto_x25519(uint8_t       shared_secret   [32],
                   const uint8_t your_secret_key [32],
                   const uint8_t their_public_key[32]);

void crypto_x25519_public_key(uint8_t       public_key[32],
                              const uint8_t secret_key[32]);


///////////////
/// Ed25519 ///
///////////////
void crypto_ed25519_public_key(uint8_t        public_key[32],
                               const uint8_t  secret_key[32]);

void crypto_ed25519_sign(uint8_t        signature[64],
                         const uint8_t  secret_key[32],
                         const uint8_t *message, size_t message_size);

int crypto_ed25519_check(const uint8_t  signature[64],
                         const uint8_t  public_key[32],
                         const uint8_t *message, size_t message_size);

////////////////////////////////
/// Authenticated encryption ///
////////////////////////////////
void crypto_ae_lock_detached(uint8_t        mac[16],
                             uint8_t       *ciphertext,
                             const uint8_t  key[32],
                             const uint8_t  nonce[24],
                             const uint8_t *plaintext,
                             size_t         text_size);

int crypto_ae_unlock_detached(uint8_t       *plaintext,
                              const uint8_t  key[32],
                              const uint8_t  nonce[24],
                              const uint8_t  mac[16],
                              const uint8_t *ciphertext,
                              size_t         text_size);

void crypto_ae_lock(uint8_t       *box,      // text_size + 16
                    const uint8_t  key[32],
                    const uint8_t  nonce[24],
                    const uint8_t *plaintext,
                    size_t         text_size);

int crypto_ae_unlock(uint8_t       *plaintext,
                     const uint8_t  key[32],
                     const uint8_t  nonce[24],
                     const uint8_t *box,     // text_size + 16
                     size_t         text_size);


///////////////////////////////////////////
/// Public key authenticated encryption ///
///////////////////////////////////////////
void crypto_lock_key(uint8_t       shared_key      [32],
                     const uint8_t your_secret_key [32],
                     const uint8_t their_public_key[32]);

void crypto_lock_detached(uint8_t        mac[16],
                          uint8_t       *ciphertext,
                          const uint8_t  your_secret_key [32],
                          const uint8_t  their_public_key[32],
                          const uint8_t  nonce[24],
                          const uint8_t *plaintext,
                          size_t         text_size);

int crypto_unlock_detached(uint8_t       *plaintext,
                           const uint8_t  your_secret_key [32],
                           const uint8_t  their_public_key[32],
                           const uint8_t  nonce[24],
                           const uint8_t  mac[16],
                           const uint8_t *ciphertext,
                           size_t         text_size);

void crypto_lock(uint8_t       *box,  // text_size + 16
                 const uint8_t  your_secret_key [32],
                 const uint8_t  their_public_key[32],
                 const uint8_t  nonce[24],
                 const uint8_t *plaintext,
                 size_t         text_size);

int crypto_unlock(uint8_t       *plaintext,
                  const uint8_t  your_secret_key [32],
                  const uint8_t  their_public_key[32],
                  const uint8_t  nonce[24],
                  const uint8_t *box,  // text_size + 16
                  size_t         text_size);

///////////////////////////////////////
/// Anonymous public key encryption ///
///////////////////////////////////////
void crypto_anonymous_lock(uint8_t       *box,   // text_size + 48
                           const uint8_t  random_secret_key[32],
                           const uint8_t  their_public_key[32],
                           const uint8_t *plaintext,
                           size_t         text_size);

int crypto_anonymous_unlock(uint8_t       *plaintext,
                            const uint8_t  your_secret_key[32],
                            const uint8_t *box,   // text_size + 48
                            size_t         text_size);

#endif // MONOCYPHER_H
