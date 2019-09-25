ifdef VMM_HOME
OPTS = +define+VMM_12 +incdir+$(VMM_HOME)/sv
else
OPTS = +define+VMM_12 -ntb_opts rvm
endif


all: clean comp run

clean:
	rm -rf simv* csrc core *.log urg* vc* ucli* 

comp: env.sv
	vcs -sverilog  $(OPTS) env.sv -l comp.log	

run:
	simv +vmm_rtl_config=RTLCFG +vmm_gen_rtl_config -l run1.log
	simv +vmm_rtl_config=RTLCFG -l run2.log
	
