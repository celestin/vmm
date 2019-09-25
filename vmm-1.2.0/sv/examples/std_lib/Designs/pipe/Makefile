CHK	= src
VMM = ../../../src
SVTB	= vcs -sverilog -PP +incdir+$(VMM)+$(CHK)

all:
	($(SVTB) $(CHK)/pipeline_example.sv\
             $(CHK)/assert_req_ack.sv \
             $(CHK)/bind_req_ack.sv ; \
             simv)
clean:
	rm -rf simv*  csrc vcdplus.vpd *~

