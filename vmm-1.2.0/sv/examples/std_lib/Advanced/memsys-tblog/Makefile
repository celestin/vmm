ifdef VMM_HOME
OPTS = +define+VMM_12 +incdir+$(VMM_HOME)/sv
else
OPTS = +define+VMM_12 -ntb_opts rvm
endif

COMP_ARGS = -debug_all -sverilog -ntb -ntb_opts dtm \
                +incdir+cpu+memsys_env+tests +define+VMM_12_UNDERPIN_STDLIB \
		$(OPTS) \
		 +define+VCS2009_12

RUN_ARGS += +vmm_tr_verbosity=debug +rvm_log_default=trace

all: clean comp test3

clean:
	rm -rf simv* csrc *.log *.txt *.fcov ._* *.sav *.vpd vc_hdrs.h
	rm -rf ucli.key .vcsmx*
	rm -rf DVE*

comp:
	vcs -sverilog $(COMP_ARGS) $(VCSFLAGS) memsys_env/memsys.test_top.sv memsys_env/memsys_tb.sv -f memsys.f -l comp.log

test1:
	./simv +vmm_test=test1 -l test1.log $(RUN_ARGS)  

test2:
	./simv +vmm_test=test2 -l test2.log $(RUN_ARGS)

test_write:
	./simv +vmm_test=test_write -l test3.log $(RUN_ARGS)

test3:
	./simv +vmm_test=test1+test2 -l test3.log $(RUN_ARGS)


dve: test1
	dve -vpd vcdplus.vpd -session memsys_session.tcl
 
