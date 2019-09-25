ifdef VMM_HOME
OPTS = +define+VMM_12 +incdir+$(VMM_HOME)/sv
else
OPTS = +define+VMM_12 -ntb_opts rvm
endif


all: clean comp run1 run2

clean:
	rm -rf simv* csrc core *.log urg* vc* ucli*

comp: env_pkg.sv tests.sv prog.sv
	vcs -sverilog  $(OPTS) env_pkg.sv tests.sv prog.sv -l comp.log	

run1: comp
	simv -l run.log +vmm_test=test1

run2: comp
	simv -l run.log +vmm_test=test2


