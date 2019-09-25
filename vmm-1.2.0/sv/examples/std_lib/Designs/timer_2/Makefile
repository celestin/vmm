VMM	= src
SVTB	= vcs -sverilog -ntb_opts vmm -PP +incdir+$(VMM)

all:
	($(SVTB) $(VMM)/timer_nooverlap.sv; simv)
debug:
	($(SVTB) $(VMM)/timer_nooverlap.sv -assert enable_diag; simv -assert success > r.txt)
clean:
	rm -rf simv*  csrc vcdplus.vpd *~ *.txt

