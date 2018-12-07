Open source case studies for Frama-C
====================================

This repository is a collection of open source C codes to be used with
[Frama-C](http://frama-c.com), in particular with the EVA
(Evolved Value Analysis) plug-in.

Each directory contains open-source code that constitutes a "case study".


# Requirements

- GNU Make >= 4.0;
- Frama-C 17 (Chlorine);
- The `frama-c` binary must be in the PATH.


# Usage

- `cd` to one of the case studies;

- Run `make` to parse and run EVA on the predefined targets
  (you can run `make help` to get the list of base targets).
  Note that the default file used by GNU Make is `GNUmakefile` if it exists.
  We use this to avoid renaming the original Makefile, if any. It also means
  that, if you want to compile the code using its Makefile, you'll have to
  explicitly name it (`make -f Makefile`).

- For each base target `t`, the following targets are generated:

    - `t.parse`: parse the sources;
    - `t.eva`: run EVA;
    - `t.eva.gui`: open the GUI.

  Each target depends on the previous one; note that `t.parse.gui` is also
  available (e.g. for inspecting the AST before the analysis).

## Optional targets

- For each base target `t`, the following optional targets are generated:

    - `t.stats`: print time/memory usage;
    - `t.parse.loop` and `t.eva.loop`: use the Loop Analysis plug-in to produce
      a file with slevel heuristics (running EVA may improve the result of
      Loop Analysis, so `t.eva.loop` should be more precise than `t.parse.loop`).
      After obtaining this initial set of parameters, consider saving it to a
      `.slevel` file and including it in the `GNUmakefile`. This way, you can
      improve the parameters for specific functions as you refine the analysis.

## Remarks

- The output of `t.eva` is verbose, but you can ignore it;
  the important information (warnings and alarms) can be inspected via the GUI;

- The result of each analysis is stored in a directory containing the full logs
  and Frama-C save files; successive runs are copied into timestamped
  directories, to allow comparing them (e.g. via `meld`);

- To try other parametrizations, simply edit variables
  `CPPFLAGS/FCFLAGS/EVAFLAGS` in `GNUmakefile` and re-run `make`.

# Notes

## Source code modifications

Only minor modifications were performed on each of these case studies:

- File `GNUmakefile` is added to each case study, with Frama-C/EVA-specific
  rules for parsing and running the analysis;
- Some case studies contain a `.slevel` file which is derived from the result
  obtained by the Loop Analysis plug-in;
- When necessary, syntactic modifications were performed to ensure better
  C99-compliance and/or the inclusion of stubs to allow Frama-C to parse the
  files;
- In some cases, an `eva_main` function was added to provide a better initial
  context for the analysis;
- When recursive calls are present, the functions containing them need to be
  replaced with specifications;
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
sources and the `GNUmakefile` that you have devised to run Frama-C.

On the other hand, if you have some interesting open-source C software
(ideally, C99-compatible) that you are unable to parse and/or run with
Frama-C/EVA, consider creating an issue with the description of the problem
you are facing (e.g. missing/incompatible declarations in the Frama-C libc,
problems when preprocessing/parsing the software, constructs unsupported
by EVA, etc). Ideally, create a (WIP) pull request with the sources in a new
directory, ready to be prepared for the case study.


# License

License files are kept in each directory where they were originally found,
when available. We also summarize the license of each directory below.

- `2048`: MIT
- `chrony`: GPL
- `debie1`: distribution and use authorized by Patria Aviation Oy,
            Space Systems Finland Ltd. and Tidorum Ltd, see `README.txt`
            and `terms_of_use-2014-05.pdf`
- `gzip124`: GPL
- `hiredis`: Redis license (BSD-style), see `COPYING`
- `icpc`: Unlicense
- `jsmn`: MIT
- `khash`: MIT
- `kilo`: BSD
- `libmodbus`: LGPL
- `mini-gmp`:  LGPL or GPL
- `monocypher`: see `README`
- `papabench`: GPL
- `polarssl-1.1.7`: GPL
- `qlz`: GPL
- `semver`: MIT
- `solitaire`: public domain (see `solitaire.c`)
- `tweetnacl-usable`: public domain (see `LICENSE.txt`)
