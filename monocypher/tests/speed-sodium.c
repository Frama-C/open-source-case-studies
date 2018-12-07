#include "speed.h"
#include "sodium.h"

static u64 chacha20(void)
{
    u8 out[SIZE];
    RANDOM_INPUT(in   , SIZE);
    RANDOM_INPUT(key  ,   32);
    RANDOM_INPUT(nonce,    8);

    TIMING_START {
        crypto_stream_chacha20_xor(out, in, SIZE, nonce, key);
    }
    TIMING_END;
}

static u64 poly1305(void)
{
    u8 out[16];
    RANDOM_INPUT(in , SIZE);
    RANDOM_INPUT(key,   32);

    TIMING_START {
        crypto_onetimeauth(out, in, SIZE, key);
    }
    TIMING_END;
}

static u64 authenticated(void)
{
    u8 out[SIZE];
    u8 mac[crypto_aead_xchacha20poly1305_ietf_ABYTES];
    RANDOM_INPUT(in   , SIZE);
    RANDOM_INPUT(key  ,   32);
    RANDOM_INPUT(nonce,    8);

    TIMING_START {
        crypto_aead_xchacha20poly1305_ietf_encrypt_detached(
            out, mac, 0, in, SIZE, 0, 0, 0, nonce, key);
    }
    TIMING_END;
}

static u64 blake2b(void)
{
    u8 hash[64];
    RANDOM_INPUT(in , SIZE);
    RANDOM_INPUT(key,   32);

    TIMING_START {
        crypto_generichash(hash, 64, in, SIZE, key, 32);
    }
    TIMING_END;
}

static u64 sha512(void)
{
    u8 hash[64];
    RANDOM_INPUT(in, SIZE);

    TIMING_START {
        crypto_hash_sha512(hash, in, SIZE);
    }
    TIMING_END;
}

static u64 argon2i(void)
{
    u8 hash [32];
    RANDOM_INPUT(password,  16);
    RANDOM_INPUT(salt    ,  16);

    TIMING_START {
        if (crypto_pwhash(hash, 32, (char*)password, 16, salt,
                          3, SIZE, crypto_pwhash_ALG_ARGON2I13)) {
            fprintf(stderr, "Argon2i failed.\n");
        }
    }
    TIMING_END;
}

static u64 x25519(void)
{
    u8 in [32] = {9};
    u8 out[32] = {9};

    TIMING_START {
        if (crypto_scalarmult(out, out, in)) {
            fprintf(stderr, "Libsodium rejected the public key\n");
        }
    }
    TIMING_END;
}

static u64 edDSA_sign(void)
{
    u8 sk       [64];
    u8 pk       [32];
    u8 signature[64];
    RANDOM_INPUT(message, 64);
    crypto_sign_keypair(pk, sk);

    TIMING_START {
        crypto_sign_detached(signature, 0, message, 64, sk);
    }
    TIMING_END;
}

static u64 edDSA_check(void)
{
    u8 sk       [64];
    u8 pk       [32];
    u8 signature[64];
    RANDOM_INPUT(message, 64);
    crypto_sign_keypair(pk, sk);
    crypto_sign_detached(signature, 0, message, 64, sk);

    TIMING_START {
        if (crypto_sign_verify_detached(signature, message, 64, pk)) {
            printf("Monocypher verification failed\n");
        }
    }
    TIMING_END;
}

int main()
{
    SODIUM_INIT;
    print("Chacha20         ",chacha20()     /DIV,"megabytes  per second");
    print("Poly1305         ",poly1305()     /DIV,"megabytes  per second");
    print("Auth'd encryption",authenticated()/DIV,"megabytes  per second");
    print("Blake2b          ",blake2b()      /DIV,"megabytes  per second");
    print("Sha512           ",sha512()       /DIV,"megabytes  per second");
    print("Argon2i, 3 passes",argon2i()      /DIV,"megabytes  per second");
    print("x25519           ",x25519()           ,"exchanges  per second");
    print("EdDSA(sign)      ",edDSA_sign()       ,"signatures per second");
    print("EdDSA(check)     ",edDSA_check()      ,"checks     per second");
    printf("\n");
    return 0;
}
