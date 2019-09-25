ifdef VMM_HOME
OPTS = +define+VMM_12 +incdir+$(VMM_HOME)/sv
else
OPTS = +define+VMM_12 -ntb_opts rvm
endif

all: clean comp run

clean:
	rm -rf simv* csrc vc_hdrs.h .vcsmx_rebuild *.log *.dat *.log work/* *.svshell *~

comp:
	vcs -sverilog   $(OPTS) +plusarg_save opts_basic.sv -l comp.log

run:
	simv +vmm_opts+i1=1+b1+s1=x+iy=5+ii=9 +vmm_i2=2 +vmm_b2 +vmm_s2=y +vmm_iz=5 +vmm_ii=5 +vmm_opts_file+./basic.opt1+./basic.opt2 -l run.log 

