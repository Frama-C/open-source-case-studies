/* C implementation of Bruce Schneier's card cipher, "Solitaire".
   Paul Crowley <paul@hedonism.demon.co.uk>, 1999
   This program is placed in the public domain.
  
   This program is mainly for performing statistical tests on 
   Solitaire's output; the actual ability to encrypt text is added
   only so that the implementation correctness can be verified.
   So the cipher core is heavily optimised but much of the supporting
   code used for actual encryption is not optimised at all, and even
   contains superfluous statistics-related work.

   http://www.hedonism.demon.co.uk/paul/solitaire/ */

#include <string.h>
#include <stdio.h>
#include <assert.h>
#include <stdlib.h>

#define STREQUAL(a,b) (strcmp(a,b) == 0)

/* State of the 54-card deck.  This keeps a spare deck for copying
   into.  It also has three spare slots *behind* the start of the
   deck: two so the deck can be moved backward if a joker is moved
   from the bottom to the top in the first step, and one so that the
   reference to the card before the first joker always points
   somewhere even when there's a joker on the top of the pack. */

typedef struct SolState_t {
    int a, b;
    int *deck, *spare;
    int deck1[57], deck2[57];
} SolState_t ;

SolState_t state;

int verbose = 0;
int lastout, cocount;


#define JOKER_STEP(var,ovar) \
    (((var != 53) ? \
      (source[var] = source[var +1], var++) : \
      (source--, ovar++, source[0] = source[1], var = 1)), \
     ((var == ovar)?(ovar--):0))

/* Cycle the state for "rounds" outputs, skipping jokers
   as usual.  "lastout" is the last output, which is never a joker.
  
   If "rounds" is zero though, cycle the state just once, even
   if the output card is a joker. "lastout" may or may not be set.
   This is only useful for key setup.
  
   Note that for performance reasons, this updates the coincidence
   statistics under all circumstances, so they need to be set to zero
   immediately before the large batch run. */

static void cycle_deck(
    int rounds
)
{
    int *source, *s, *sb, *d;
    int lo, hi;
    int nlo, nhi, nccut;
    int output;

    do {
        assert(state.a != state.b);
        assert(state.deck[state.a] == 53);
        assert(state.deck[state.b] == 53);
        source = state.deck;
        JOKER_STEP(state.a,state.b);
        JOKER_STEP(state.b,state.a);
        JOKER_STEP(state.b,state.a);
        source[state.a] = 53;
        source[state.b] = 53;
        if (state.a < state.b) {
            lo = state.a;
            hi = state.b + 1;
        } else {
            lo = state.b;
            hi = state.a + 1;
        }
        nlo = 54 - hi;
        nhi = 54 - lo;
            /* We do both the triple cut and the count cut as one
               copying step; this means handling four separate cases. */
        nccut = source[lo -1];
        s = source;
        if (lo == 0) {
                /* There's a joker on the top of the pack.  This can
                   only happen in one exact circumstance, but when it
                   does nccount is wrong.  So we handle it specially. */
            assert(state.a == 0);
            assert(state.b == 2);
            d = &state.spare[51];
            sb = &source[3];
            while(s < sb) {*d++ = *s++;}
            d = &state.spare[0];
            sb = &source[54];
            while(s < sb) {*d++ = *s++;}
            state.a = 51;
            state.b = 53;
        } else if (nccut <= nlo) {
                /* The second cut is before the first joker. */
            d = &state.spare[nhi - nccut];
            sb = &source[lo -1];
            while(s < sb) {*d++ = *s++;}
            state.spare[53] = *s++;
            d = &state.spare[nlo - nccut];
            sb = &source[hi];
            while(s < sb) {*d++ = *s++;}
            d = &state.spare[53 - nccut];
            sb = &source[nccut + hi]; /* ccut */
            while(s < sb) {*d++ = *s++;}
            d = &state.spare[0];
            sb = &source[54];
            while(s < sb) {*d++ = *s++;}
            state.a += nlo - nccut - lo;
            state.b += nlo - nccut - lo;
        } else if (nccut < nhi) {
                /* The second cut is between the two jokers */
            d = &state.spare[nhi - nccut];
            sb = &source[lo -1];
            while(s < sb) {*d++ = *s++;}
            state.spare[53] = *s++;
            d = &state.spare[53 - nccut + nlo];
            sb = &source[nccut - nlo + lo]; /* ccut */
            while(s < sb) {*d++ = *s++;}
            d = &state.spare[0];
            sb = &source[hi];
            while(s < sb) {*d++ = *s++;}
            d = &state.spare[53 - nccut];
            sb = &source[54];
            while(s < sb) {*d++ = *s++;}
            if (state.a < state.b) {
                state.a = 53 - nccut + nlo;
                state.b = nhi - nccut -1;
            } else {
                state.b = 53 - nccut + nlo;
                state.a = nhi - nccut -1;
            }
        } else {
                /* The second cut is after the last joker. */
            d = &state.spare[53 - nccut + nhi];
            sb = &source[nccut - nhi]; /* ccut */
            while(s < sb) {*d++ = *s++;}
            d = &state.spare[0];
            sb = &source[lo -1];
            while(s < sb) {*d++ = *s++;}
            state.spare[53] = *s++;
            d = &state.spare[53 - nccut + nlo];
            sb = &source[hi];
            while(s < sb) {*d++ = *s++;}
            d = &state.spare[53 - nccut];
            sb = &source[54];
            while(s < sb) {*d++ = *s++;}
            state.a += 53 - nccut + nlo - lo;
            state.b += 53 - nccut + nlo - lo;
        }
        source = state.deck; 
        state.deck = state.spare;
        state.spare = source;
        output = state.deck[state.deck[0]];
        if (output >= 26) {
            if (output >= 52) {
                if (output > 52)
                    continue;
                output = 0;
            } else {
                output -= 26;
            }
        }
        cocount += (lastout == output);
        lastout = output;
        rounds--;
    } while (rounds > 0);
}

static void print_deck(
) 
{
  int i;

  //@ loop unroll 54;
  for (i = 0; i < 54; i++) {
    if (state.deck[i] < 53) {
      putchar(' ' + state.deck[i]);
    } else if (i == state.a) {
      putchar('U');
    } else {
      assert(i == state.b);
      putchar('V');
    }
  }
}

/* Key the deck with a passphrase. */

static void key_deck(
    char *key
)
{
    int i, kval, *tmp;

    state.deck = state.deck1 + 3;
    state.spare = state.deck2 + 3;
    //@ loop unroll 52;
    for (i = 0; i < 52; i++) {
        state.deck[i] = i+1;
    }
    state.deck[state.a = 52] = 53;
    state.deck[state.b = 53] = 53;
    for (; *key != '\0'; key++) {
        if ( *key >= 'A' && *key <= 'Z' ) {
            cycle_deck(0); /* Special value '0' is only useful here... */
                /* And now perform a second count cut based on the key letter */
            kval = *key - 'A' + 1;
            //@ loop unroll 53;
            for (i = 0; i < 53; i++)
                state.spare[i] = state.deck[(i + kval) % 53];
            state.spare[53] = state.deck[53];
            if (state.a != 53)
                state.a = (state.a + 53 - kval) % 53;
            if (state.b != 53)
                state.b = (state.b + 53 - kval) % 53;
            tmp = state.deck;
            state.deck = state.spare;
            state.spare = tmp;
	    if (verbose) {
	        print_deck();
	        printf(" after %c\n", *key);
	    }
        }
    }
    /* These are touched by the keying: fix them. */
    lastout = 100; cocount = 0;
}

/* Encrypt a single character. */

static char encrypt_char(
    char char_in
)
{
    char char_out;

    cycle_deck(1);
    char_out = 'A' + (char_in - 'A' + lastout) % 26;
    if (verbose) {
        print_deck();
        printf(" %c -> %c\n", char_in, char_out);
    }
    return char_out;
}


int main(
    int argc,
    char *argv[]
)
{
    char **av = argv, *tmp;
    int slow_mode = 0;
    long rounds;

    /* Skip the name of the program */
    av++; argc--;
    if (argc  < 2) {
      printf("Usage: [flags] key message|len\n");
    }
    //@ loop unroll 3;
    while (argc > 2) {
      if (STREQUAL(*av, "-v")) {
	verbose = 1;
      } else if (STREQUAL(*av, "-s")) {
	slow_mode = 1;
      } else {
	printf ("Unrecognised flag: %s\n", *av);
	exit(-1);
      }
      av++; argc--;
    }
    key_deck(av[0]);
    rounds = strtol(av[1], &tmp, 0);
    if (*tmp != '\0') {
      /* It's not a number - so it's a string! */
      char *text = av[1];
      int i = 0;

      //@ loop unroll 256;
      for (; *text != '\0'; text++) {
	if (*text >= 'A' && *text <= 'Z') {
	  if (i > 0 && (i % 5) == 0)
	    putchar(' ');
	  putchar(encrypt_char(*text));
	  i++;
	}
      }
      while ((i % 5) != 0) {
	putchar(encrypt_char('X'));
	i++;
      }
      putchar('\n');
    } else {
      /* Treat it as a sequence of 'A's. */
      int i;

      if (rounds <= 0) {
	printf("Rounds number must be greater than zero\n");
	exit(-1);
      }
      if (verbose || slow_mode) {
	for (i = 0; i < rounds; i++)
	  encrypt_char('A');
      } else {
	cycle_deck(rounds);
      }
      printf("Coincidences: %d / %ld\n", cocount, rounds -1);
    }
    return 0;
}

#ifdef __FRAMAC__
# include "__fc_builtin.h"
volatile int nondet;
// main for EVA
int eva_main() {
  int argc = Frama_C_interval(0, 5);
  char argv0[256], argv1[256], argv2[256], argv3[256], argv4[256];
  char *argv[5] = {argv0, argv1, argv2, argv3, argv4};
  //@ loop unroll 5;
  for (int i = 0; i < 5; i++) {
    Frama_C_make_unknown(argv[i], 255);
    argv[i][255] = 0;
  }
  return main(argc, argv);
}
#endif // __FRAMAC__
