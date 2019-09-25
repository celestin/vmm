VMM	= src
SVTB	= vcs -sverilog -PP +incdir+$(VMM)

all:
	($(SVTB) $(VMM)/figure7_3.sv;    simv)

clean:
	rm -rf simv*  csrc vcdplus.vpd *~

