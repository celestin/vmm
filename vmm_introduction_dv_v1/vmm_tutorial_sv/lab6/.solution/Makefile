#-----------------------------------------------------------------------------
#
# SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary work of
# Synopsys, Inc., and is fully protected under copyright and trade secret
# laws. You may not view, use, disclose, copy, or distribute this file or
# any information contained herein except pursuant to a valid written
# license from Synopsys.
#
#-----------------------------------------------------------------------------
#
# Filename    : $Id: Makefile,v 1.7 2006/06/05 14:56:39 kevork Exp $
#
# Created by  : Synopsys Inc. 09/01/2004
#               $Author: kevork $
#
# Description : Makefile for RVM-SV labs
#
#-----------------------------------------------------------------------------

default: lab

################## COMMON #########################

VCS = vcs

RTL = apb/apb_if.sv hdl/top.v  hdl/mem.v

OPT = -sverilog -debug_all -ntb_opts rvm

INC = +incdir+apb+env

CMP =

RUN = 
DIR = $(shell basename `pwd`)

################## VCS #########################

lab1: build_01 run

lab2:
	$(VCS) $(OPT) $(INC) $(RTL) tests/test_02.sv -R $(CMP)

lab3: build_03 run

lab4: build_04 run

lab5: build_05 run

lab6: build_06 run

lab7: build_07 run

cov:
	urg -dir .

build_%:
	$(VCS) $(OPT) $(INC) $(RTL) tests/test_$*.sv $(CMP)

run:
	./simv $(RUN)

################## HELP #########################

help:
	@echo "gmake - run this lab using VCS"

################## Clean #########################

clean:
	@rm -rf *.vro simv* csrc* *.vshell depchk*vr */*~
	@rm -rf .__snps* *.db* *.vpd* *.log *~ obj scs* work DVEfiles
	@rm -rf *.fcov *.html .vhdl.assert* .vlog.assert* vc_hdrs.h
	@rm -rf pioneer_shell.v pioneer.vdb pioneer.config transcript virsim.cfg


                                                                        
                                                                        
                                                                        
                                                                        
                                                                        
                                                                        
                                                                        
                                                                        
                                                                        
                                                                        
                                                                        
                                                                        
                                                                        
                                                                        
                                                                        
                                                                        
                                                                        
                                                                        
                                                                        
lab: lab6
