This directory contains a set of C files, that should be annotated with ACSL
specifications and proved with Frama-C WP. In most cases, the specification
should be quite obvious from the function name and the code, but below are some
hints on the main points of interest for each example. Furthermore, for each
`file.c` in this directory, there is a completely annotated
`../Solutions/file.c` that can be proved by Frama-C/WP. Basic knowledge of
C, ACSL and `frama-c` is assumed.

# 01-swap.c

## Minimal contract

The basic specification of the `swap` function is that at the end of the
function the values pointed to by `a` and `b` have been exchanged, i.e. we
need two `ensures` clauses describing the new value of `*a` (resp. `*b`) in
terms of the former value of `*b`, that is `\at(*b, Pre)` (resp. `\at(*a, Pre)`)
These two clauses can be trivially validated by
`frama-c -wp 01-swap.c -then -report` (or `frama-c-gui -wp 01-swap.c` for
the GUI version)

## Taking run-time errors into account

What we have proved above is that the post-conditions hold **if the function
returns successfully**. However, we haven't so far verified anything about
potential runtime errors (_undefined behaviors_ in terms of ISO C standard).
It is possible to ask WP to prove the absence of runtime errors as well by
adding `-wp-rte` as an option to the command line.

This time, the minimal contract is not sufficient to prove all verification
conditions. Indeed, our `swap` function only works if we call it with `\valid`
pointers as arguments, and we have to add pre-conditions for that. Once
the pre-conditions are added, everything should be proved.

# 02-permut.c

In this example, we attempt to use `swap` twice in order to permut the
values contain in three pointers. The example provides a sample contract
for `swap`, but you can use your own instead.

A first important point is that the provided contract for `swap` is not
complete: we do not specify the _frame condition_ of `swap`, i.e. the
`assigns` clause that indicates which memory locations `swap` might modify.
When specifying callees of the entry point of the verification, it is
**mandatory** to put such clauses in the specification. Otherwise, WP cannot
make any assumption on the memory state after the call.

There is also a subtle pre-condition for `permut`: namely, if the three
pointers are aliased, the results will not be a real permutation (for instance,
if `a == c`, the first call to swap will overwrite the value pointed to by `c`):
we really want to call `permut` with `\separated` pointers.
