#!/bin/csh -f
if (! $?VMM_HOME) then
 set COMP_ARGS = (-sverilog -ntb_opts uvm+rvm +define+VMM_ON_TOP +incdir+../../../src +incdir+../../../src/hfpb +incdir+../../../src/hfpb_components)
else
 set COMP_ARGS = (-sverilog +incdir+${VMM_HOME}/sv+${UVM_HOME}/src+${UVM_VMM_INTEROP}/src +incdir+../../../src +incdir+../../../src/hfpb +incdir+../../../src/hfpb_components +define+VMM_ON_TOP +define+VMM_IN_PACKAGE)
endif

vcs $COMP_ARGS -l comp.log test.sv
