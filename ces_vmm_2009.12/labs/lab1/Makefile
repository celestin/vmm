# Makefile for VMM Lab1
TB_TOP = ./test.sv
SEED = 1
TEST = Default
LOG = NORMAL

default: all 

all: compile_no_warn run

run:
	./simv +vmm_log_default=$(LOG) -l simv.log +ntb_random_seed=$(SEED) +vmm_test=$(TEST)

random:
	./simv +vmm_log_default=$(LOG) -l simv.log +ntb_random_seed_automatic +vmm_test=$(TEST)

compile_no_warn:
	vcs -sverilog -ntb_opts rvm -timescale="1ns/100ps" -l comp.log -debug_all +warn=noBCNACMBP $(TB_TOP)

compile:
	vcs -sverilog -ntb_opts rvm -timescale="1ns/100ps" -l comp.log -debug_all $(TB_TOP)

dve:
	dve -vpd vcdplus.vpd &

dve_i:
	./simv -l simv.log -gui -tbug +ntb_random_seed=$(SEED) +vmm_test=$(TEST)

solution: clean
	cp ../../solutions/lab1/*.sv .

clean:
	rm -rf simv* csrc* *.tmp *.vpd *.key log *.h temp *.log .vcs* *.txt

nuke: clean
	rm -rf *.v* *.sv .*.lock .*.old DVE* *.tcl *.h
	cp ../../solutions/lab1/tb_env.sv.orig tb_env.sv
	cp ../../solutions/lab1/test_cfg.sv.orig test_cfg.sv
	cp ../../solutions/lab1/psdisplay.sv .

help:
	@echo =======================================================================
	@echo  " 								       "
	@echo  " USAGE: make target <SEED=xxx> <LOG=YYY> <TEST=ZZZ>                    "
	@echo  " 								       "
	@echo  "  xxx is the random seed.  Can be any integer except 0. Defaults to 1  "
	@echo  "  YYY sets the vmm_log filter.  Defaults to NORMAL                     "
	@echo  "  ZZZ selects the vmm test.     Defaults to Default                    "
	@echo  " 								       "
	@echo  " ------------------------- Test TARGETS ------------------------------ "
	@echo  " all             => Compile TB and DUT files and run the simulation.   "
	@echo  " compile         => Compile TB and DUT files                           "
	@echo  " compile_no_warn => Compile without warning for un-populated contraint "
	@echo  " run             => Run the simulation with SEED.                      "
	@echo  " random          => Run the simulation with random seed.               "
	@echo  " dve             => Run dve in post-processing mode                    "
	@echo  " dve_i           => Run simulation interactively with dve              "
	@echo  " clean           => Remove all intermediate simv and log files.        "
	@echo  "                                                                       "
	@echo  " -------------------- ADMINISTRATIVE TARGETS ------------------------- "
	@echo  " help       => Displays this message.                                  "
	@echo  " solution   => Copies all files from solutions directory               "
	@echo  " nuke       => Erase all changes. Put all files back to original state "
	@echo  "								       "
	@echo =======================================================================

