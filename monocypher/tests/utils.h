#ifndef UTILS_H
#define UTILS_H

#include <inttypes.h>
#include <stddef.h>
#include <stdio.h>

typedef int8_t   i8;
typedef uint8_t  u8;
typedef uint32_t u32;
typedef int32_t  i32;
typedef int64_t  i64;
typedef uint64_t u64;

#define FOR(i, start, end) for (size_t (i) = (start); (i) < (end); (i)++)
#define SODIUM_INIT                                 \
    if (sodium_init() == -1) {                      \
        printf("Libsodium init failed.  Abort.\n"); \
        return 1;                                   \
    }
#define RANDOM_INPUT(name, size) u8 name[size]; p_random(name, size)

static void store64_le(u8 out[8], u64 in)
{
    out[0] =  in        & 0xff;
    out[1] = (in >>  8) & 0xff;
    out[2] = (in >> 16) & 0xff;
    out[3] = (in >> 24) & 0xff;
    out[4] = (in >> 32) & 0xff;
    out[5] = (in >> 40) & 0xff;
    out[6] = (in >> 48) & 0xff;
    out[7] = (in >> 56) & 0xff;
}

u64 load64_le(const u8 s[8])
{
    return (u64)s[0]
        | ((u64)s[1] <<  8)
        | ((u64)s[2] << 16)
        | ((u64)s[3] << 24)
        | ((u64)s[4] << 32)
        | ((u64)s[5] << 40)
        | ((u64)s[6] << 48)
        | ((u64)s[7] << 56);
}

// Pseudo-random 64 bit number, based on xorshift*
u64 rand64()
{
    static u64 x = 12345; // Must be seeded with a nonzero value.
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    return x * 0x2545F4914F6CDD1D; // magic constant
}

void p_random(u8 *stream, size_t size)
{
    // note: unrolling up to 8192 removes 2 alarms,
    // but increases analysis by 3 minutes
    //@ loop unroll 480;
    FOR (i, 0, size) {
        stream[i] = (u8)rand64();
    }
}

void print_vector(u8 *buf, size_t size)
{
    FOR (i, 0, size) {
        printf("%hhx%hhx", buf[i] >> 4, buf[i] & 0x0f);
    }
    printf(":\n");
}

void print_number(u64 n)
{
    u8 buf[8];
    store64_le(buf, n);
    print_vector(buf, 8);
}

#endif // UTILS_H
