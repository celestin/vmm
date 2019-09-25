CHK	= src
VMM = ../../../src
SVTB	= vcs -sverilog -ntb_opts vmm -PP +incdir+$(VMM)+$(CHK) +define+ASSERT_ON+COVER_ON

all:
	($(SVTB) $(CHK)/*.sv;    simv)

clean:
	rm -rf simv*  csrc vcdplus.vpd *~

