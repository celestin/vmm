ifdef VMM_HOME
OPTS = +define+VMM_12 +incdir+$(VMM_HOME)/sv
else
OPTS = +define+VMM_12 -ntb_opts rvm
endif

COMP_ARGS = -debug_all -sverilog -ntb -ntb_opts dtm \
                +incdir+cpu+memsys_env+tests +define+VMM_12_UNDERPIN_STDLIB \
		$(OPTS) \

all: clean comp test1 test2 test_write

clean:
	rm -rf simv* csrc *.log *.txt *.fcov ._* *.sav *.vpd vc_hdrs.h
	rm -rf ucli.key .vcsmx*

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

