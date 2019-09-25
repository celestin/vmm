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
	simv +vmm_FOO_INT=99 +vmm_FOO_STR=NEW_VAL +vmm_FOO_BIT -l run.log
