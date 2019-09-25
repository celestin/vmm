#!/bin/csh -f

setenv VCS_HOME /fs/Release/solaris_Base_32
set path = ($VCS_HOME/bin $path)
setenv LM_LICENSE_FILE 7183@minerva

vcs -R -sverilog -f ../bin/rtl_file_list.lst -f ../bin/vcs_sim_file_list.lst -f ../bin/vcs_xilinx_file_list.lst\
        +incdir+../../../bench/verilog+../../../rtl/verilog +define+SIM+ETH_FIFO_XILINX+XILINX_RAMB4+REGR \
        -l vcs.log -PP +vcs+vcdpluson +verilog2001ext+.v 
