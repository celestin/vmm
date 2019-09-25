CHK	= src
VMM = ../../../src
SVTB	= vcs -sverilog -PP +incdir+$(VMM)+$(CHK) +define+ASSERT_ON+COVER_ON

all:
	($(SVTB) $(CHK)/quiesent_state_tb.sv  $(CHK)/assert_quiescent_state.sv ; simv)

clean:
	rm -rf simv*  csrc vcdplus.vpd *~
