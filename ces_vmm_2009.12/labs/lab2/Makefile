# Makefile for VMM Lab2
TB_TOP = ./test.sv
SEED = 1
TEST = Default
LOG = NORMAL

all: compile_no_warn run

run:
	./simv +vmm_log_default=$(LOG) -l simv.log +ntb_random_seed=$(SEED) +vmm_test=$(TEST)

random:
	./simv +vmm_log_default=$(LOG) -l simv.log +ntb_random_seed_automatic +vmm_test=$(TEST)

force:
	./simv +vmm_force_verbosity=$(LOG) -l simv.log +ntb_random_seed=$(SEED)

compile_no_warn:
	vcs -sverilog -ntb_opts rvm -timescale="1ns/100ps" -l comp.log -debug_all +warn=noBCNACMBP $(TB_TOP)

compile:
	vcs -sverilog -ntb_opts rvm -timescale="1ns/100ps" -l comp.log -debug_all $(TB_TOP)

dve:
	dve -vpd vcdplus.vpd &

dve_i:
	./simv -l simv.log -gui -tbug +ntb_random_seed=$(SEED) +vmm_test=$(TEST)

copy: clean
	cp ../../solutions/lab1/*.sv .
	rm tb_env.sv
	cp ../../solutions/lab2/tb_env.sv.orig tb_env.sv

mycopy: clean
	cp ../lab1/*.sv .

solution: clean
	cp ../../solutions/lab2/*.sv .

clean:
	rm -rf simv* csrc* *.tmp *.vpd *.key log *.h temp *.log .vcs* *.txt

nuke: clean
	rm -rf *.v* *.sv .*.lock .*.old DVE* *.tcl *.h *.orig

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
	@echo  " copy            => Continue lab with files from solutions directory   "
	@echo  " mycopy          => Continue lab with files from user directory        "
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
