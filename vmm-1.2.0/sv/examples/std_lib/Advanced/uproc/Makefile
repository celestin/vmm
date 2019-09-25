ifdef VMM_HOME
OPTS = +define+VMM_12 +incdir+$(VMM_HOME)/sv
else
OPTS = +define+VMM_12 -ntb_opts rvm
endif

all: comp run 

clean:
	\rm -rf simv* csrc *.vpd *.tcl  work/* core* *.svshell vc_hdrs*

comp:
	vcs $(OPTS) -sverilog -debug_all test.sv -l comp.log

run:
	simv -l run.log
