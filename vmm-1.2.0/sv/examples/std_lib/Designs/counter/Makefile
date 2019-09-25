VMM	= src
SVTB	= vcs -sverilog -PP +incdir+$(VMM)

all:
	($(SVTB) $(VMM)/counter_example.sv;    simv)

clean:
	rm -rf simv*  csrc vcdplus.vpd *~

