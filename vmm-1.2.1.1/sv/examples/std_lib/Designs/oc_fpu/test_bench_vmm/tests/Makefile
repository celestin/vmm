## 
## -------------------------------------------------------------
##    Copyright 2004-2009 Synopsys, Inc.
##    All Rights Reserved Worldwide
## 
##    Licensed under the Apache License, Version 2.0 (the
##    "License"); you may not use this file except in
##    compliance with the License.  You may obtain a copy of
##    the License at
## 
##        http://www.apache.org/licenses/LICENSE-2.0
## 
##    Unless required by applicable law or agreed to in
##    writing, software distributed under the License is
##    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
##    CONDITIONS OF ANY KIND, either express or implied.  See
##    the License for the specific language governing
##    permissions and limitations under the License.
## -------------------------------------------------------------
##

FPU	= ../fpu
ENV	= ../env
TESTS   = ../tests
HDL     = ../../verilog

SIMV	= simv

CC	= gcc 

ifdef VMM_HOME
OPTS = +incdir+$(VMM_HOME)/sv
else
OPTS = +define+VMM_12 -ntb_opts rvm
endif

RUNOPTS =
COMPLOG = vcs.log
RUNLOG = simv.log

HDL_FILES = $(HDL)/except.v $(HDL)/pre_norm.v $(HDL)/fpu.v $(HDL)/pre_norm_fmul.v $(HDL)/post_norm.v $(HDL)/primitives.v

all: compile run

compile: 
	vcs -sverilog +define+VMM_TB \
	$(ENV)/top.v $(ENV)/fpu_i.sv $(TESTS)/test_00_trivial.sv \
	$(HDL_FILES) \
	./regex_library.c \
	+incdir+$(ENV) +incdir+$(FPU) +incdir+$(VMM_HOME)/sv \
	$(OPTS) -o $(SIMV) -l $(COMPLOG) -cc $(CC)

run:
	$(SIMV) $(RUNOPTS) -l $(RUNLOG)
	
clean: 
	rm -rf *.vrh *.vro *.vrl simv* csrc *_shell.v \
	*.log *.db *.html *.fcov \
	._* core *.key random *.dump *.vpd ag* opendatabase.log \
	session.tcl* $(COMPLOG) $(RUNLOG) vc_hdrs.h
