ifdef VMM_HOME
OPTS = +define+VMM_12 +incdir+$(VMM_HOME)/sv
else
OPTS = +define+VMM_12 -ntb_opts rvm
endif

all: comp run

comp:
	vcs -sverilog top.sv -debug_pp -timescale="1ns/1ps" -debug_all $(OPTS)

clean:
	rm -rf vcdplus.vpd  simv* csrc vc_hdrs.h  .vcsmx_rebuild
	rm -rf gen.dat bad_log

run:
	./simv +vmm_test=test1+test2 +vmm_opts+num_of_dl_pusc_subchannels=28@%phy_cfg_inst_string_name -l run.log
