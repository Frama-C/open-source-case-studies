This directory contains the material for the Frama-C/WP tutorial given
at [VerifyThis](http://www.pm.inf.ethz.ch/research/verifythis.html) during
[ETAPS'19](https://conf.researchr.org/home/etaps-2019).

The `Examples` directory contains the source code of the examples presented
during the tutorial, without specifications. Interested readers can try to
provide their own ACSL annotations to prove the correctness of the functions
(and fix any issue they might find along their work). For each example, a
similarly named file exists in the `Solutions` directory, with a formal
specification completely proved using the WP plug-in of Frama-C 18.0, together
with the Alt-Ergo solver and the Coq proof assistant. See the Installation
section below for setting up an appropriate environment. Finally,
the `Slides` directory contains the TeX sources and the pdf of the slides that
have been presented.

# Installation

This section only give a brief overview on installing Frama-C, Alt-Ergo
and Coq on a standard Linux distribution. More thorough instructions are
available on the main [Frama-C repository](https://github.com/Frama-C/Frama-C-snapshot/blob/master/INSTALL.md). Basically, if Frama-C 18.0, Alt-Ergo >=2.0, and
Coq >= 8.5 are available in your distribution, you can just install the
corresponding packages.

Otherwise, these three tools mainly rely on
the OCaml Package Manager [`opam`](https://opam.ocaml.org), widely available
across Linux distributions. Basically, once you've installed `opam`, the
following commands should give you an appropriate environment for verifying
programs with Frama-C/WP, including its GUI

1. opam install depext
2. opam depext lablgtk frama-c alt-ergo coq
3. opam install lablgtk frama-c alt-ergo coq

# Acknowledgements

I wish to thanks the VerifyThis organizers for inviting me to give
this tutorial.
