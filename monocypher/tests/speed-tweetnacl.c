#include "speed.h"
#include "utils.h"
#include "tweetnacl.h"

static u64 salsa20(void)
{
    u8 out[SIZE];
    RANDOM_INPUT(in   , SIZE);
    RANDOM_INPUT(key  ,   32);
    RANDOM_INPUT(nonce,    8);

    TIMING_START {
        crypto_stream_salsa20_xor(out, in, SIZE, nonce, key);
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
    u8 out[SIZE + 32];
    RANDOM_INPUT(in   , SIZE + 32);
    RANDOM_INPUT(key  ,        32);
    RANDOM_INPUT(nonce,         8);

    TIMING_START {
        crypto_secretbox(out, in, SIZE + 32, nonce, key);
    }
    TIMING_END;
}

static u64 sha512(void)
{
    u8 hash[64];
    RANDOM_INPUT(in, SIZE);

    TIMING_START {
        crypto_hash(hash, in, SIZE);
    }
    TIMING_END;
}

static u64 x25519(void)
{
    u8 in [32] = {9};
    u8 out[32] = {9};

    TIMING_START {
        crypto_scalarmult(out, out, in);
    }
    TIMING_END;
}

static u64 edDSA_sign(void)
{
    u8 sk        [ 64];
    u8 pk        [ 32];
    u8 signed_msg[128];
    unsigned long long sig_size;
    RANDOM_INPUT(message, 64);
    crypto_sign_keypair(pk, sk);

    TIMING_START {
        crypto_sign(signed_msg, &sig_size, message, 64, sk);
    }
    TIMING_END;
}

//int crypto_sign     (u8 *sm, u64 *smlen, const u8 *m , u64 n, const u8 *sk);
//int crypto_sign_open(u8 *m , u64 *mlen , const u8 *sm, u64 n, const u8 *pk);

static u64 edDSA_check(void)
{
    u8 sk        [ 64];
    u8 pk        [ 32];
    u8 signed_msg[128];
    u8 out_msg   [128];
    unsigned long long sig_size;
    unsigned long long msg_size;
    RANDOM_INPUT(message, 64);
    crypto_sign_keypair(pk, sk);
    crypto_sign(signed_msg, &sig_size, message, 64, sk);

    TIMING_START {
        if (crypto_sign_open(out_msg, &msg_size, signed_msg, sig_size, pk)) {
            printf("TweetNaCl verification failed\n");
        }
    }
    TIMING_END;
}

int main()
{
    print("Salsa20          ",salsa20()      /DIV,"megabytes  per second");
    print("Poly1305         ",poly1305()     /DIV,"megabytes  per second");
    print("Auth'd encryption",authenticated()/DIV,"megabytes  per second");
    print("Sha512           ",sha512()       /DIV,"megabytes  per second");
    print("x25519           ",x25519()           ,"exchanges  per second");
    print("EdDSA(sign)      ",edDSA_sign()       ,"signatures per second");
    print("EdDSA(check)     ",edDSA_check()      ,"checks     per second");
    printf("\n");
    return 0;
}
