Open source case studies for Frama-C
====================================

This repository is a collection of open source C codes to be used with
[Frama-C](http://frama-c.com), in particular with the EVA
(Evolved Value Analysis) plug-in.

Except for the `fcscripts` directory (which contains a Makefile and some helper
scripts), each directory contains open-source code that constitutes a
"case study".


# Requirements

- GNU Make >= 4.0;
- Frama-C 15 (Phosphorus);
- The `frama-c` binary must be in the PATH.


# Usage

- `cd` to one of the case studies;

- Run `make` to parse and run EVA on the predefined targets
  (you can run `make help` to get the list of base targets);

- For each base target `t`, the following targets are generated:

    - `t.parse`: parse the sources;
    - `t.eva`: run EVA;
    - `t.eva.gui`: open the GUI.

  Each target depends on the previous one; note that `t.parse.gui` is also
  available (e.g. for inspecting the AST before the analysis).

## Remarks

- The output of `t.eva` is verbose, but you can ignore it;
  the important information (warnings and alarms) can be inspected via the GUI;

- The result of each analysis is stored in a directory containing the full logs
  and Frama-C save files; successive runs are copied into timestamped
  directories, to allow comparing them (e.g. via `meld`);

- To try other parametrizations, simply edit variables
  `CPPFLAGS/FCFLAGS/EVAFLAGS` in the case study Makefiles and re-run `make`.

# Notes

## Source code modifications

Only minor modifications were performed on each of these case studies:

- If there is a `Makefile` in the root directory of a case study,
  it is systematically renamed to `original.mk`;
- A `Makefile` is added to each case study,
  with Frama-C/EVA-specific rules for parsing and running the analysis;
- When necessary, syntactic modifications were performed to ensure better
  C99-compliance and/or the inclusion of stubs to allow Frama-C to parse the
  files;
- The `main` function may have been modified (or added, if none existed) to
  ensure a more useful initial context;
- Some ACSL annotations may have been added to the sources
  (to illustrate their usage, or to improve the analysis).


## Rationale

- The main objectives of these files are:

    1. Non-regression tests;

    2. Benchmarking;

  Therefore, some of the code bases are voluntarily parametrized with
  suboptimal parameters, for non-regression testing; alternatively, some
  code bases may be present several times, with different versions and/or
  parametrizations;

- These case studies constitute work in progress and do not represent
  "finalized" case studies.


# Contributions

If you know of other open source code bases where Frama-C/EVA produces
interesting results, please contribute with pull requests including the
sources and the `Makefile` that you have devised to run Frama-C.


# License

License files are kept in each directory where they were originally found,
when available. We also summarize the license of each directory below.

- `2048`: MIT
- `bzip2-1.0.6`: bzip2 license (BSD-style), see `LICENSE`
- `debie1-e-free`: distribution and use authorized by Patria Aviation Oy,
                   Space Systems Finland Ltd. and Tidorum Ltd, see `README.txt`
                   and `terms_of_use-2014-05.pdf`
- `fcscripts`: LGPL
- `gzip124`: GPL
- `hiredis`: Redis license (BSD-style), see `COPYING`
- `khash`: MIT
- `libmodbus`: LGPL
- `mini-gmp`:  LGPL or GPL
- `monocypher`: see `README`
- `monocypher-0.6-tweaked`: see `README`
- `PapaBench-0.4`: GPL
- `polarssl-1.1.7`: GPL
- `qlz`: GPL
- `solitaire`: public domain (see `solitaire.c`)
- `tweetnacl-usable`: public domain (see `LICENSE.txt`)
- `unqlite`: 2-clause BSD (see http://unqlite.org/licensing.html)
