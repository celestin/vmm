
--------------------------------------------------------------------------------
Title: VMM Kit 1.1c
--------------------------------------------------------------------------------

This kit contains a version of VMM 1.1 that is qualified to run on Questa and
IUS and intended to run on all three simulators. Modifications were needed to
make it SV-compliant and to workaround differences in simulator implementations.

Setup typically involves the setting of two environment variables, as 
precompiled DPI shared libraries for Linux, Windows, and SunOS platforms are
provided.

--------------------------------------------------------------------------------
Group: Library Setup
--------------------------------------------------------------------------------

Simulator requirements:


  Mentor Questa - 6.4a or later
  Cadence IUS   - 8.2-p001 or later
  Synopsys VCS  - X.X or later

  make          - GNU make v3.80 or later (needed for IUS)
  

Platforms supported:

  linux     - Intel and AMD x86-based architectures;
              SUSE Linux Enterprise Server 9.0, 9.1, 10; 
              Red Hat Enterprise Linux 3, 4, 5; 32- and 64-bit;
  
  sunos5    - v8, 9, and 10, 32-bit only
  
  sunos5x86 - v10, 32- and 64-bit
   
  Windows   - (Questa only) XP and Vista, 32-bit only (tested on XP)
 

Environment variables:

The following environment variables must be set before running the
examples.

  VMM_HOME    - the VMM library install location, if running outside
                the current installation area.

  VMM_DPI_DIR - Needed when running the included examples, this variable
                contains the path to the pre-compiled DPI libraries in
                ~$VMM_HOME/shared~. This path is dependent on the platform
                used. Its default value is set for 64-bit Linux platforms.


Windows cygwin users must follow special requirements for setting
these environment variables. See instructions toward the bottom of this
README file.


--------------------------------------------------------------------------------

Group: Examples

--------------------------------------------------------------------------------

All examples can be found at ~$VMM_HOME/sv/examples~.

Before attempting to run the examples, review <Interop Library Setup> to check
that your environment meets minimum requirements and that the appropriate
environment variables have been set.

Running all examples in a leaf-level directory:

To run all examples residing in a leaf-level directory, first ~cd~ to the
directory.

  | prompt> cd $VMM_HOME/sv/examples/std_lib/wishbone

Then type one of the following commands, depending on your simulator.

  | prompt> ./run_questa.sh           Questa
  | prompt> make -f Makefile.ius all  IUS
  | prompt> make -f Makefile.vcs all  VCS

To clean a directory of all run-time files, type one of the following
commands.

  | prompt> ./run_questa.sh clean       Questa
  | prompt> make -f Makefile.ius clean  IUS
  | prompt> make -f Makefile.vcs clean  VCS


Running all examples (Questa only):

To run all the examples, ~cd~ to the top-level examples
directory and execute the appropriate Makefile

  | prompt> cd $VMM_HOME/sv/examples
  | prompt> ./run_questa.sh

To clean all examples of run-time files, type

  | prompt> ./run_questa.sh clean


Platform-specific dependencies and limitations:

This kit ships with precompiled libraries for Linux, Windows, Sun Sparc,
and Sunos5x86 platforms. All examples import DPI-C routines and shared
libraries. 

See the Release Notes for information on general platform support.
The examples have the following platform-specific limitations.

  - The perf/tl_bus example has two sub-examples: sqltxt and sqlite. The latter
    will not run on Sun Sparc platforms at this time.

  - Synopsys ships the ralgen utility as a binary for Linux and Sun Solaris
    platforms only. Thus, on win32 and Sunos5x86 platforms, examples using
    ralgen to generate code instead copy pre-generated output to the work
    area.

Note- VCS users may run the examples using the Makefiles that ship with the
original distribution. For convenience, these same Makefiles are included in
this kit as Makefile.vcs.


--------------------------------------------------------------------------------

Group: Windows Users

--------------------------------------------------------------------------------


  Windows users running on cygwin must take care to specify paths in env
  variables to work around the different filepath formats used between
  Windows OS and cygwin.

  Setting VMM_HOME:

  These env variables must start with C: and use backslashes as the delimiter.

  | setenv VMM_HOME 'C:\cygwin\installs\vmm_1.1c'

  We enclose the path in tick quotes to prevent the cygwin shell from
  interpreting the backslashes.


  Setting PATH:

  You need to augment your PATH env variable so that Windows can
  find dependent DLLs when loading.

  | setenv PATH "$VMM_HOME\\shared\\bin\\win32:$PATH"

  The double quotes are used in case your existing PATH contains spaces.
  We must preceed each backslash in the path with the escape character,
  which also happens to be a backslash.


  Setting VMM_DPI_DIR:

  The VMM_DPI_DIR must be set in a particular way to work around the different
  filepath specs between cygwin and ~vsim~. With VMM_HOME set as above,
  the VMM_DPI_DIR should be set as follows

  | setenv VMM_DPI_DIR \\cygwin/installs/vmm_1.1c/shared/bin/win32
  
  Note that the path starts with a backslash and omits the drive letter.
  Thereafter, the path is a normal Unix path with forward-slash as the
  delimiter.


--------------------------------------------------------------------------------

Group: License

--------------------------------------------------------------------------------

   Copyright 2008-2009 Mentor Graphics Corporation
   All Rights Reserved Worldwide
   
   Licensed under the Apache License, Version 2.0 (the "License"); you may
   not use this file except in compliance with the License.  You may obtain
   a copy of the License at
   
          http://www.apache.org/licenses/LICENSE-2.0
   
   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
   WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
   License for the specific language governing permissions and limitations
   under the License.



