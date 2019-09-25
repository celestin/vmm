CHK	= src
VMM = ../../../src
SVTB	= vcs -sverilog -PP +incdir+$(VMM)+$(CHK)

all:
	($(SVTB) $(CHK)/dl_pl_sva_checker.sv \
             $(CHK)/clk_gen.sv \
             $(CHK)/dl_pl_dut.sv \
             $(CHK)/dl_pl_mdut.sv \
             $(CHK)/top_all_vlog.sv ; \
             simv)
clean:
	rm -rf simv*  csrc vcdplus.vpd *~

