FPU	= ../fpu
ENV	= ../env
TESTS   = ../tests
HDL     = ../../verilog
VMM_HOME = /remote/vtghome5/badri/VMM/src

SIMV	= simv

CC	= gcc 

OPTS = 
RUNOPTS =
COMPLOG = vcs.log
RUNLOG = simv.log

HDL_FILES = $(HDL)/except.v $(HDL)/pre_norm.v $(HDL)/fpu.v $(HDL)/pre_norm_fmul.v $(HDL)/post_norm.v $(HDL)/primitives.v

all: compile run

compile: 
	vcs -sverilog +define+VMM_TB \
	$(ENV)/top.v $(ENV)/fpu_i.sv $(TESTS)/test_00_trivial.sv \
	$(HDL_FILES) \
	$(VMM_HOME)/work_arounds/regex_library.c \
	+incdir+$(ENV) +incdir+$(FPU) +incdir+$(VMM_HOME) \
	$(OPTS) -o $(SIMV) -l $(COMPLOG) -cc $(CC)

run:
	$(SIMV) $(RUNOPTS) -l $(RUNLOG)
	
clean: 
	rm -rf *.vrh *.vro *.vrl simv* csrc *_shell.v \
	*.log *.db *.html *.fcov \
	._* core *.key random *.dump *.vpd ag* opendatabase.log \
	session.tcl* $(COMPLOG) $(RUNLOG) vc_hdrs.h
