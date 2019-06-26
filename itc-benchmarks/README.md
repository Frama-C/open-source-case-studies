itc-benchmarks
==============

This is a modified version of the
[itc-benchmarks Github](https://github.com/regehr/itc-benchmarks)
repository, with tests from the Toyota InfoTechnology Center,
made available online by John Regehr.

Several patches have been applied to the original sources to deal with:

- Issues found in the original code
  (e.g. copy-paste typos and undefined behaviors (UBs));
- Recursive calls (commented out for running Eva);
- Portability issues (e.g. casts `pthread_t -> int`).


## Renamings

- The `.` in directory names was replaced with `_`
  to avoid issues with analysis scripts;

- `02_wo_Defects/free_nondynamically_allocated_memory.c` was renamed to
  `02_wo_Defects/free_nondynamic_allocated_memory.c`, to match the equivalent
  file in `01_w_Defects`.


Tests out of scope
==================

Concurrency and recursive calls are not yet handled by Eva.
Therefore, all tests whose defects concern threads and concurrency are not
handled by Eva.
Also, some kinds of defects that do not imply undefined behavior, such as
redundant conditions in tests, are out of the scope of Frama-C/Eva.
However, such tests are still left in the code, since they allow us to detect
unexpected undefined behaviors (e.g. as detailed later for `redundant_code.c`).


Applied patches
===============

The list of applied patches is separated into three categories:

- Likely unintentional typos;
- Unforeseen undefined behaviors;
- Limitations for Eva.

The first category comprises errors which look like simple unintended typos.

The second contains some code that invokes undefined behavior, but does not
seem caused by a simple typo.

Finally, the last category contains mostly commented out calls to recursive
functions.


## Typos

- `buffer_underrun_dynamic.c`, function `dynamic_buffer_underrun_037`:

        doubleptr[0][0]='T'; // the first '0' should have been 'i'

- `littlemem_st.c`, functions `littlemem_st_008_func_002`,
  `littlemem_st_009_func_002`, `littlemem_st_010_func_002` and
  `littlemem_st_011_func_002`: the same copy-paste error was made in these
  four functions, in which the global variable name copied from function 007
  was not updated. This results in code referring to a different variable,
  leading to possible runtime errors during execution. Fixing each reference
  to the corresponding global variable (as was clearly intended in the code)
  prevents false alarms.

- `redundant_code.c`, function `redundant_cond_009`:

    The comment before the function suggests the loop condition, in the
    `02_wo_Defects` version, should be `a > 10` (or `10 < a`).
    This is also closer to the code in the `01_w_Defects` version.
    Interestingly, the inversion leads to undefined behavior, since the
    value of `a` will cycle through all negative values, before being
    decremented and wrapping around, causing a signed overflow.
    Fixing the condition is necessary to prevent UB in the `02_wo_Defects`
    version.


## Undefined behavior

- `data_lost.c`, function `data_lost_006`, and also `data_overflow`, functions
  `data_overflow_024` and `data_overflow_025`:

    Float to int conversions which overflow (larger than the maximum integer
    value for the corresponding type) are undefined behavior. While the UB is
    deliberate in the `01_w_Defects` directory, there is also UB in the
    `02_wo_Defects` directory. The code was patched to a value that fits in the
    integer type.


- `invalid_memory_access.c`, function `invalid_memory_access_003`:

    A char pointer `c` is passed to `malloc` then `free`, and then assigned to
    another pointer (`psink = c`). This last assignment (after `c` has been
    freed) entails the access to an indeterminate value (the dangling pointer),
    which Eva detects as UB. It is not necessary to keep the assignment in the
    `01_w_Defects` directory, since there is already an UB earlier in the code.
    The instruction was removed from both versions of the file.


- `overrun_st.c`, several functions `overrun_st_XXX`:

    These functions all follow the same pattern, which results in accessing an
    uninitialized variable. As an example, here is the code of `overrun_st_001`
    (without defects):

        void overrun_st_001 ()
        {
          char buf[5];
          buf[4] = 1;
          sink = buf[idx];
        }

    `idx` is a global variable, default-initialized to 0. Therefore, the last
    statement, `sink = buf[idx]` (likely introduced to avoid compiler warnings
    about "unused variable buf"), will access uninitialized memory. This
    situation happens 37 times in the file. A simple patch in all cases
    consists in 0-initializing the arrays by adding ` = {0}` to their
    declarations. this removes the unintentional errors in the `02_wo_defects`
    version, without removing the intended errors in `01_w_defects`.


- `st_overflow.c`, function `st_overflow_006_func_001`:

    Same issue as previously: a local array without initializer has its element
    accessed, even in the `02_wo_defects` version. The same solution is applied:
    the array is 0-initialized by adding `= {0}` to its declaration.


- `bit_shift.c`, function `bit_shift_009`:

    The code performs a left-shift of a signed value, `1 << (rand() % 32)`.
    However, `1 << 31` (the maximum possible value) has type `signed int`.
    In a 32-bit architecture (as is assumed for this set of benchmarks),
    this leads to a signed overflow, which is undefined behavior.
    The patch consists in replacing `rand() % 32` with `rand() % 31`.


- `st_underrun.c`, functions `st_underrun_002_func_001` and
  `st_underrun_007_func_001` (only the `02_wo_defects` version):

    The no-defects versions of these functions actually still contain some
    undefined behavior. This is the code of `st_underrun_002_func_001`:

        void st_underrun_002_func_001 (st_underrun_002_s_001 s) {
          int len = strlen(s.buf) - 1;
          for (;s.buf[len] != 'Z';len--) {
            if ( len < 0 ) break;
          }
        }

    `s.buf` initially contains `"STRING"` (therefore no 'Z's).
    When `len` reaches 0, the test inside the loop is still false, so
    we return to the loop decrement, `len` becomes -1, and then we
    test `s.buf[-1] != 'Z'`. This causes an out-of-bounds access,
    leading to undefined behavior.
    The code likely intended to return -1 when the character is not
    found, but since the value of `len` is not actually used here, we
    can simply replace the inner test with `len <= 0` to avoid the
    undefined behavior.
    The same patch is applicable to `st_underrun_007_func_001`.


- `st_underrun.c`, function `st_underrun_007`:

    This function also suffers from the uninitialized access issue mentioned
    in file `overrun_st.c`: variable `st_underrun_007_s_001` only has the first
    element of array `buf` initialized (to 1), while the remaining of the array
    is left uninitialized. When `st_underrun_007_func_001` is called, there is
    an access to the uninitialized values of `s.buf` inside `strlen`.
    The same patch as for `overrun_st.c` (adding `= {0}` to the declaration)
    also works here.


- `ptr_subtraction.c`, function `ptr_subtraction_001`:

    The no-defects version contains a subtraction between pointers of different
    bases (`buf1 - buf2`) which itself leads to undefined behavior. It is
    necessary to comment out this instruction (and the one using its result).


## Limitations for Eva

Eva does not handle recursive calls yet, so a few tests containing them had
the recursive calls commented out:

- `invalid_memory_access.c`, function `invalid_memory_access_005`;
- `st_overflow.c`, function `st_overflow_005_func_001`;
- `st_underrun.c`, function `st_underrun_005`.


Also, 2 test files had deliberate parsing errors (concerning function pointers)
which prevent Frama-C from parsing them. They were removed from the list of
files to be parsed and their functions commented out from `main`.

Also, 5 tests concerning concurrency were removed because their source files
perform a non-portable cast from `pthread_t` to `int` (POSIX states that
the type of `pthread_t` is not required to be an arithmetic type. Frama-C's
libc defines it with a `struct`, which is allowed by the standard, and chosen
to deliberately help identify such non-conformance violations.
Lastly, since the tests are out of the scope of Eva anyway, removing them has
no impact in the end.


Remaining alarms
================

A few alarms remain in the code, due to:

- Imprecision in the handling of the variadic function `snprintf`:
  this function assigns to a buffer, which is then passed to `strlen`.
  However, there is currently no way to emulate the precise behavior of
  what `snprintf` produces, therefore we use a safe approximation in which the
  string is possibly non-terminated. This leads to 2 alarms (one in the caller
  and another in the callee).

- Signed overflows in `02_wo_Defects/redundant_code.c`, functions
  `redundant_cond_009` and `redundant_cond_0013`:

    Even after fixing the loop condition as mentioned previously,
    Eva is not able to infer that there is no signed overflow in the loop.
    This is because the value of `a` is imprecise (the range `[10..32767]`
    inside the loop) and very large, so a huge number of iterations would
    be necessary to obtain a precise result (that is, that the sum
    `32767 + 32766 + ... + 10`, stored in `b`, does not overflow a 32-bit int).
    Frama-C/Eva performs a widening which leads to a spurious alarm about
    the signed overflow.


"False negatives"
=================

A few test cases in the `01_w_Defects` do not lead to alarms in Frama-C/Eva.
These test cases are related to situations in which, from the point of view
of the user, it might make sense to consider them as "defects", but from the
point of view of the C standard, they are perfectly valid situations.

One such case is in file `memory_allocation_failure.c`, function
`memory_allocation_failure_002`:

    long long int *ptr=(long long*) malloc(MAX_VAL *sizeof(long long));

`MAX_VAL` is defined as `UINT_MAX`, therefore an unsigned integer type.
The test intention was that the size should "overflow".
However, unsigned overflow is allowed by the C standard, therefore
Frama-C by default does not raise any alarms.

It is possible to use option `-warn-unsigned-overflow` to trigger an alarm
in this situation, but then the rest of the code needs to be patched to avoid
triggering it in other situations.
In particular, the same file `memory_allocation_failure.c` contains the
following variable declaration:

    static unsigned int static_var = MAX_VAL*2;

Which makes the analysis stop during global variable initialization, since a
definite alarm has been found.
Fixing such issues should allow Frama-C to detect the overflow in the call
to `malloc`.
