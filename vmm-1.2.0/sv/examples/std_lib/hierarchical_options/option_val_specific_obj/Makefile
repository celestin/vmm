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
	simv +vmm_opts+FOO_INT=99@d2:b1+FOO_INT=1050@d2:c2:b1+FOO_BIT@d2:b1+FOO_BIT@d2:c2:b1+FOO_STR=NEW_VAL1@d2:b1+FOO_STR=NEW_VAL2@d2:c2:b1  -l run.log
