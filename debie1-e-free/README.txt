This is the DEBIE-1 DPU SW benchmark, version "e"

This software is provided by courtesy of its developers and IP owners:
Patria Aviation Oy, Space Systems Finland Oy, and Tidorum Ltd.

The software is provided under the specific conditions set forth in the
Terms Of Use document enclosed with or attached to this software. The
Terms Of Use document should be in a file called terms_of_use-2014-05.pdf;
if you do not find that file near this README file, ask for it from the
source from where you got this README. Do not use the SW before you have
read the Terms Of Use. Note that, prior to May 2014, this same benchmark
was distributed under much less permissive Terms of Use. Check that the
Terms of Use that you find are signed on 5.5.2014 by Harri Lähti for
Patria Aviation Oy and on 8.5.2014 by Tuomas TalviOja for Space Systems
Finland Oy and by Niklas Holsti for Tidorum Ltd.

The DEBIE-1 DPU SW was developed by Space Systems Finland for Patria
Aviation, to control the DEBIE-1 instrument, which was carried on
the European Space Agency'S PROBA-1 satellite. The DEBIE-1 instrument
observes micro-meteoroids and small space debris by detecting impacts
on its sensors, both mechanically and electrically. A later version,
DEBIE-2, was mounted on the International Space Station.

This version of the DEBIE-1 DPU SW has been modified by Tidorum to adapt
it for use as a benchmark (originally for the WCET Tool Challenge,
http://www.mrtc.mdh.se/projects/WTC/). To distinguish the original SW
from the benchmark, we suggest that the benchmark should be called the
"debie1 benchmark" (lower case, omit "DPU").

This version of the benchmark includes a port to the MPC5554 target
contributed by Simon Wegener of AbsInt Angewandte Informatik GmbH. The
port consists of some target-specific header files, a build script, and
an executable binary file. The Terms of Use apply to this port, too.

For more information about the DEBIE-1 benchmark, please refer to
the Wiki site of the WCET Tool Challenge 2014, at:

http://www.irit.fr/wiki/doku.php?id=wtc:benchmarks:debie1

(However, it may be a while before that web page is updated for the
new, less restrictive Terms of Use, so please ignore any out-of-date
information regarding earlier terms of use on that web page.)


CHANGES RELATIVE TO VERSION "d"

- The port to the mpc5554/gcc target is changed to place the
  64-ko array "data_memory", that simulates the "external data
  memory" of the original DEBIE-1 computer (an 80C32), in the
  ".externalram" segment, that is, in memory that is not on
  the MPC5554 chip. The reason for this change is that the
  64-ko array is too large to fit in the internal SRAM. This
  change is again courtesy of Simon Wegener, AbsInt GmbH.
  The change is in the target-specific source file "target.c".
  A new binary (debie1.elf) is included.


CONTENTS

The folder "orig-docs" contains some development documentation for
the original DEBIE-1 DPU SW. It is provided as a help to understanding
the architecture and functionality of the debie1 benchmark, but NOTE
that the benchmark is, in many respects, significantly different
from the original DEBIE-1 DPU SW -- for one thing, the benchmark
has been reduced to a single-threaded program, where the original
SW was multi-threaded and ran under a pre-emptive real-time kernel.
So some parts of these documents do not apply to the benchmark.

The folder "code" contains the 'C' source-code of the debie1 benchmark.
The main "code" folder contains the target-independent (portable)
parts of the source-code, without the test-cases, too.

The subfolder code/harness contains the source-code parts that
simulate the DEBIE-1 DPU (Data Processing Unit) peripherals and
run the test-cases. This code is portable, too, but it is not part
of the original DEBIE-1 DPU flight software. The main module is
harness.c; the rest of the files in code/harness are headers that
introduce the harness interface into the DEBIE-1 DPU SW header
files. For example, the header file code/harness/target_ad_conv.h
extends code/ad_conv.h and makes the software use the simulated A/D
conversion functions in harness.c.

There are subfolders for each target and cross-compiler as follows:

code/intel/linux

   Compilation for an Intel/Linux system using the native
   GCC compiler. The compiled program (debie1, not included in
   this archive) runs the test cases currently written in the
   harness module once. If the macro TRACE_HARNESS is defined, the
   benchmark then stops, otherwise it sticks in the eternal loop
   in debie1.c. The code should be fully portable to other
   32-bit computers, eg Intel/Windows, but the build script may
   need adjustments.

code/arm7-lpc2138-mam/gcc-if07

   Cross-compilation for the NXP LPC2138 using the GNU ARM
   compiler that comes with the IF-DEV-LPC development kit,
   updated to Build 118 from www.isystem.com. The build script
   needs files (start-up and run-time code) from the folder
   arm7-lpc2138-mam/gcc-if07, see below.

   The LPC2138 is configured with MAM enabled (mode 2) and
   the PLL set to generate a 60 MHz clock frequency.

   The compiled program (debie1.elf, included in this archive)
   repeatedly runs the test cases in harness.c, and blinks the
   LED now and then (about every 25 sec).

code/mpc5554/gcc

   Cross-compilation for the MPC5554 target using GCC. This port
   was contributed by Simon Wegener of AbsInt Angewandte Informatik
   GmbH. The build script target-build.sh generates an executable
   that runs the test cases in harness.c once and then enters the
   eternal loop in the main() function. By default this executable
   generates no output (and no RapiTime trace). The folder contains
   an ELF binary called debie1.elf that Simon generated with
   target-build.sh and the GNU crosstools from CodeSourcery's
   G++ lite gcc package (available at
   http://www.codesourcery.com/sgpp/lite/power). In this version
   of the benchmark, both internal SRAM and external RAM are used.

Each target subfolder contains the following target- and
compiler-specific files:

   keyword.h

      Type and macro definitions for this target and cross-compiler.

   problems.h

      Macro definitions for marking the start and end of specific
      WCC'08 "analysis problems" in the test part of harness.c.
      May need other header files, eg. for RapiTime.

   target.c

      Target-specific test-harness operations.

   target_xxx.h

      Target-specific parts of the DEBIE-1 header files, if it
      is necessary to override those in code/harness.

   build.sh, build.bat, or target-build.sh etc.

      A script to compile and link the benchmark.

The folder "arm7-lpc218-mam/gcc-if07" (note, this is not the one under
"code") contains files needed by "code/arm7-lpc2183-mam/gcc-if07": a setup
script, a linker script, and run-time support files: crt0.s, crt_asyst.c,
intvec.s, cpulib.c.

To generate the binary executable for a given target and cross-compiler,
"cd" to the corresponding subfolder of "code", check that the path
definitions in the build script (build.sh, target-build.sh, or build.bat
and the corresponding setup.sh or setup.bat) are suitable for your
workstation, and execute the build script.

For running and debugging the program on the iF-DEV-LPC, the winIDEA
IDE from iSYSTEM is convenient.

--
Tidorum/NH
2014-05-13
