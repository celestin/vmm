OC_CORE_WITH_SVA  = vcs -R -sverilog  -l vcs.log -PP +vcs+vcdpluson \
	+verilog2001ext+.v +define+SIM+ETH_FIFO_XILINX+XILINX_RAMB4+REGR+ETH_WISHBONE_B3+ASSERT_ON+COVER_ON+ASSERT_INIT_MSG \
	-f ../bin/rtl_file_list.lst -f ../bin/vcs_sim_file_list.lst -f ../bin/vcs_xilinx_file_list.lst \
	+incdir+../../../../../VIP/ethernet+../../../bench/verilog+../../../rtl/verilog+../../../../../Designs/stack/src+../../../../../../src

SVA_WISHBONE = ../../../../../VIP/wishbone/master_chk.sv \
		../../../../../VIP/wishbone/slave_chk.sv \
		../../../../../VIP/wishbone/wb_chk_coverage.sv +define+SVA_WISHBONE

SVA_MII = ../../../../../VIP/ethernet/mii_sva_types.sv \
	../../../../../VIP/ethernet/mii_sva_checker.sv +define+SVA_MII


default: all

all: 
	$(OC_CORE_WITH_SVA) $(SVA_WISHBONE) $(SVA_MII)

wishbone: 
	$(OC_CORE_WITH_SVA) $(SVA_WISHBONE)

mii :  
	$(OC_CORE_WITH_SVA)  $(SVA_MII)

clean :  
	rm -rf simv* csrc *~ *.log vc_*.h *.vpd *.key
       
