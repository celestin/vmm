# Makefile for VMM Lab4
RTL_TOP = ./test_top.sv
RTL= ./router_io.sv ../../rtl/router.v
BADRTL= ../../rtl/bad/router.v
TB_TOP = ./test.sv
TEST = Default
SEED = 1
LOG = NORMAL

all: compile_no_warn run

bad: compile_bad_no_warn run

run: clean_urg
	./simv +vmm_log_default=$(LOG) -l simv.log +ntb_random_seed=$(SEED) +vmm_test=$(TEST)
	urg -dir simv.vdb
	urg -dir simv.vdb -format text

random: clean_urg
	./simv +vmm_log_default=$(LOG) -l simv.log +ntb_random_seed_automatic +vmm_test=$(TEST)
	urg -dir simv.vdb
	urg -dir simv.vdb -format text


compile_no_warn:
	vcs -sverilog -ntb_opts rvm -timescale="1ns/100ps" -l comp.log -debug_all +warn=noBCNACMBP $(RTL_TOP) $(RTL) $(TB_TOP)

compile_bad_no_warn:
	vcs -sverilog -ntb_opts rvm -timescale="1ns/100ps" -l comp.log -debug_all +warn=noBCNACMBP $(RTL_TOP) $(BADRTL) $(TB_TOP)

compile:
	vcs -sverilog -ntb_opts rvm -timescale="1ns/100ps" -l comp.log -debug_all $(RTL_TOP) $(RTL) $(TB_TOP)

dve:
	dve -vpd vcdplus.vpd &

dve_i:
	./simv -l simv.log -gui -tbug +ntb_random_seed=$(SEED) +vmm_test=$(TEST)

copy: nuke
	cp ../../solutions/lab3/*.sv .
	rm Packet_atomic_gen.sv
	rm tb_env.sv
	rm test.sv
	cp ../../solutions/lab4/send.sv .
	cp ../../solutions/lab4/recv.sv .
	cp ../../solutions/lab4/test_top.sv .
	cp ../../solutions/lab4/router_io.sv .
	cp ../../solutions/lab4/test.sv.orig test.sv
	cp ../../solutions/lab4/tb_env.sv.orig tb_env.sv
	cp ../../solutions/lab4/RcvSbCallbacks.sv.orig RcvSbCallbacks.sv
	cp ../../solutions/lab4/GenCovCallbacks.sv.orig GenCovCallbacks.sv
	cp ../../solutions/lab4/GenSbCallbacks.sv.orig GenSbCallbacks.sv
	cp ../../solutions/lab4/test_scenario.sv.orig test_scenario.sv

mycopy: nuke
	cp ../lab3/*.sv .
	rm Packet_atomic_gen.sv
	cp ../../solutions/lab4/send.sv .
	cp ../../solutions/lab4/recv.sv .
	cp ../../solutions/lab4/test_top.sv .
	cp ../../solutions/lab4/router_io.sv .
	cp ../../solutions/lab4/RcvSbCallbacks.sv.orig RcvSbCallbacks.sv
	cp ../../solutions/lab4/test_scenario.sv.orig test_scenario.sv

solution: nuke
	cp ../../solutions/lab4/*.sv .

clean:
	rm -rf simv* csrc* *.tmp *.vpd *.key log *.h temp *.log .vcs* *.txt

clean_urg:
	rm -rf *.tmp *.vpd *.key log *.h temp *.log .vcs* simv.vdb urgReport

nuke: clean clean_urg
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

