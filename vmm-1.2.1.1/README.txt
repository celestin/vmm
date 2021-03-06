------------------------------------------------------------
Title: Getting Started

(C) Copyright 2004-2010 Synopsys, Inc.
All Rights Reserved Worldwide


This section provides some recommendations for getting started with 
the VMM distribution and UVM/VMM Interop Kit.

The VMM distribution is licensed under the Apache License,
Version 2.0 (the "License"); you may not use the content of
this distribution except in compliance with the License.

The UVM/VMM interop kit distribution is licensed under the Apache License,
Version 2.0 (the "License"); you may not use the content of
this distribution except in compliance with the License.

You may obtain a copy of the License at
        http://www.apache.org/licenses/LICENSE-2.0

Group: Content of distribution
-----------------------

Topic: Distribution 

This distribution consists of VMM source code, UVM/VMM Interop Kit, 
collateral, on-line reference guides and utilities.

Distribution deliverables:

  - Source code for the VMM Standard Library (v1.13)
  - Source code for the VMM Register Abstraction Layer (v1.16)
  - Source code for the VMM Scoreboard Package (v1.5)
  - Source code for the VMM Performance Analyzer (v1.1)
  - Source code for the VMM Hardware Abstraction Layer (v2.2)
  - Source code for the UVM/VMM Interop Kit (v0.2)
  - VMM template generator
  - Linux and Solaris binaries for RAL Model Generator (v1.17)
  - PDF for the VMM Standard Library User's Guide
  - PDF for the VMM Register Abstraction Layer User's Guide
  - PDF for the VMM Scoreboard Package User's Guide
  - PDF for the VMM Performance Analyzer User's Guide
  - PDF for the VMM Hardware Abstraction Layer User's Guide
  - HTML class documentation for VMM developers
  - HTML class documentation for UVM/VMM Interop Kit
  - Source code for all examples

The Environment Composition Package (vmm_subenv, vmm_consensus) is
included as part of the VMM Standard Library.

The Memory Allocation Manager (vmm_mam) is included as part of the VMM
Register Abstraction Layer.

-----------------------
Topic: Directory Structure
The main elements of the directory structures in this distribution
are:

(start  code)
  README.txt .................... This file
  NOTICE.txt .................... Intellectual property notice
  RELEASE.txt ................... Release notes for version 1.2
  VCS2009.06.txt................. Release notes for using VCS2009.06
  VCS2009.12.txt................. Release notes for using VCS2009.12
  vmm_versions .................. Distribution verification script
  patch_vcs ..................... Script to patch a VCS installation(*)
  doc/ .......................... User and Developer Documentation
      pdf/ ...................... PDF User Guides
      devel/ .................... Developper's Class Reference
            index.html .......... Top-level HTML file
  sv/
     vmm.sv ..................... Standard library top-level file
     vmm_ral.sv ................. RAL/MAM top-level file
     vmm_sb.sv .................. Scoreboard package top-level file
     vmm_perf.sv ................ Performane Analyzer package top-level file
     vmm_hw.sv .................. HAL top-level file
     std_lib/ ................... Standard Library source files
     RAL/ ....................... RAL source files source files
     sb/ ........................ Scoreboard package source files
     perf/ ...................... Performance Analyzer package source files
     HAL/ ....................... HAL source files
     uvm_vmm_interop/
              src/ .............. UVM/VMM Interop Kit Source code
              examples .......... UVM/VMM Interop Kit Examples
     examples/ .................. Examples
              std_lib/ .......... Basic VMM examples (including VMM 1.2)
              subenv/ ........... Environment composition example
              RAL/ .............. RAL example
              sb/ ............... Scoreboard package example
              perf/ ............. Performance Analyzer package example
              HAL/ .............. HAL example
              std_lib/Advanced/ . More advanced VMM 1.2 examples
  shared/
         bin/ ................... Tool binaries and Scripts
         lib/
             templates/ ......... Code templates used by 'vmmgen'
(end)

(*) Use at your own risk! Will disable OpenVera/SystemVerilog
    interoperability!

    To maintain OpenVera/SystemVerilog interoperability,
    use the 1.2-SvOv distribution to apply the patch.


-----------------------
Group: IEEE Compliance

The SystemVerilog source code is believed to be 100% compliant with
the IEEE P1800-2005 standard. Any non-compliant usage is unintentional
and will be fixed if reported.

The examples are provided with Makefiles targetted for the VCS
simulator. They are intended as a demonstration only and do not imply
that VCS is required to use the VMM code. Any simulator compliant with
the IEEE P1800 standard should be able to compile and execute the
examples, after a suitable modification of the Makefiles.

The source code contains some VCS-specific code included within
_"`ifdef VCS/`endif"_ regions. The VCS-specific code enables some
additional VMM-awareness functionality with VCS and/or DVE as well as
provides some built-in functions for greater run-time performance
rather than using the DPI. The VCS-specific code is *NOT* required to
correctly simulate the VMM source code.

Any reference to the OpenVera (OV) language in the documentation
refers to the OV implementation of the VMM library, which is not
included in this distribution. OpenVera or an OpenVera simulator is
not required to use VMM. Any reference to the Vera or VCS simulator in
the documentation is for illustration of how to use VMM with those
specific tools. The Vera or VCS simulators are not required to use
VMM.

This version of the VMM library and examples require the following
version of the VCS simulator:

       VCS2009.12-3 or later


---------------------------
Group: Installing the distribution

Installation of VMM requires only unpacking the distribution in a
convenient location.  No additional installation procedures or scripts
are necessary.

   | % mkdir /some/path
   | % cd /some/path
   | % tar xvfz -c path/vmm-1.2.XX.tgz

---------------------------
Group: Using VMM

This section provides step-by-step guidelines to use VMM standard library 
base classes with VCS.

Topic: Step 1 - Set your VMM_HOME environment variable

You must define the environment variable "VMM_HOME" to the path
containing the unpackaged distribution. This environment variable
is required to run some examples and scripts. It also eases the
specification of the location where to pick-up the source file.

   | % setenv VMM_HOME /some/path/vmm-distrib

If you have the VCS simulator installed and properly set-up, you can
check the content of the distribution by using the command:

  | % $VMM_HOME/vmm_versions

You should add $VMM_HOME/shared/bin to your command search path to
be able to use the tools and scripts included in the distribution.

   | % setenv PATH $VMM_HOME/shared/bin:$PATH

Scripts require that "perl" be visible in your command path. Tools are
distributed in binary form for Linux and Solaris. Should you be
running on a different operating system or hardware architecture,
please contact Synopsys to obtain a suitable version of the tool
binaries.
   | % setenv VMM_HOME path/vmm-distrib
   | % vcs -sverilog +incdir+$VMM_HOME/sv

Topic: Step 2 - Include VMM standard library in your SystemVerilog code

You can make the VMM Standard Library visible to your SystemVerilog
code by including the file "<vmm.sv>".

   | `include "vmm.sv"

Topic: Step 3 - Compile VMM standard library along with your SystemVerilog code

It will be necessary to specify where the VMM source files are located
on the compilation command line. This can easily be done via the
+incdir command-line option and the VMM_HOME environment variable.

   | % ... +incdir+$VMM_HOME/sv ...

When used on a non-VCS simulator, it will be necessary to include the
file $VMM_HOME/sv/std_lib/vmm_str_dpi.c to supply the regular
expression string matching library. 

Similarly, it may be necessary to
include the file $VMM_HOME/sv/std_lib/vmm_xvc_dpi.c to supply the XVC
command parsing and execution library. Please refer to your
simulator's documentation on how to include a DPI library.

Topic: Step 4 - Additional VMM Applications

You can make a VMM Application package visible to your
SystemVerilog code by including the file corresponding to the
application package:

   Register Abstraction Layer          <vmm_ral.sv>
   Scoreboarding Package               <vmm_sb.sv>
   Performance Analyzer Package        <vmm_perf.sv>
   Hardware Abstraction Layer          <vmm_hw.sv >or <vmm_hw_rtl.sv>

Using the VMM Hardware Abstraction Layer with an architecture other
than the VMM_HW_ARCH_NULL architecture requires software and hardware
provided by emulation, acceleration or prototyping vendors. This
software is not included in this distribution and must be obtained
from the appropriate sources.

---------------------------
Group: Using UVM/VMM Interop Kit

This section provides step-by-step guidelines to use these libraries with VCS:
  - VMM standard library base classes
  - UVM base classes
  - UVM/VMM Interop Kit

Topic: Step 1 - Set your environment variables

You must define the "VMM_HOME", "UVM_VMM_INTEROP" and "UVM_HOME" environment variables.
These variables should be set to the the path
containing the unpackaged distributions. These environment variables
are required to run some examples and scripts. It also eases the
specification of the location where to pick-up the source files.

   | % setenv VMM_HOME /some/path/vmm-distrib
   | % setenv UVM_HOME /some/path/uvm-distrib
   | % setenv UVM_VMM_INTEROP ${VMM_HOME}/sv/uvm_vmm_interop

Topic: Step 2 - Add includes to your SV files

You must include the UVM and VMM libraries in your top SV file.
Note that the "uvm_vmm_pkg.sv" file is implicitly loaded in VMM package,
hence it's not necessary to add a `include statement for it.

   | `include "uvm_pkg.sv"
   | `include "vmm.sv"

Topic: Step 3 - Add +incdir and +define to your VCS command line

You must add one +incdir for each library and define the UVM_ON_TOP or
VMM_ON_TOP depending upon your testbench topology.
You also need to add +define+VMM_IN_PACKAGE to ensure VMM standard library is
embedded in a package.

   |   vcs -sverilog your_sv_files \
   |       +incdir+$(VMM_HOME)/sv \
   |       +incdir+$(UVM_VMM_INTEROP)/src \
   |       +incdir+$(UVM_HOME)/src \
   |       +define+UVM_ON_TOP   \
   |       +define+VMM_IN_PACKAGE

