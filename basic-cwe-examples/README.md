Basic CWE Examples
==================

This directory contains a few CWE examples based on some of the top CWEs from
2019 (https://cwe.mitre.org/top25/archive/2019/2019_cwe_top25.html).

It serves to illustrate basic functions from Frama-C/Eva and its graphical
interface.

This does not constitute a "case study" per se, but it should help beginners
have an idea of what Frama-C/Eva can report.

The bugs present in the test cases can easily be fixed and the analysis run
again, to see the difference.

In most cases, comments in the beginning of the file indicate helpful analysis
options and their effect. Each target has a `-precise` variant
(e.g. `cwe119-precise.eva`) which applies these extra options.
