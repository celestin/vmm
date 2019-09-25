## 
## -------------------------------------------------------------
##    Copyright 2004-2008 Synopsys, Inc.
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


VMM	= +incdir+$(VMM_HOME)/sv
#VMM	= -ntb_opts rvm
MII	= ../../ethernet
WB	= ../../wishbone
TB	= ../tb_top.sv +incdir+$(WB)+$(MII)+../..

DUTDIR  = $(VMM_HOME)/shared/examples/oc_ethernet/rtl
DUT	= -F $(DUTDIR)/rtl_file_list.lst +incdir+$(DUTDIR)

#SVA_CHECKER = +define+VCD+ASSERT_ON+COVER_ON+IMPLEMENTED_CG+IMPLEMENTED_ASSUME+SVA_CHECKERS+SVA_VMM_LOG_ON -assert enable_diag  -assert filter -assert quiet+report
SVA_CHECKER = 

OPTS	= 

VCS	= vcs -R -sverilog +verilog1995ext+.v $(VMM) \
              -ntb_opts dtm +warn=noBCNACMBP

all: test_trivial_tx test_trivial_rx test_unconstrained

test_%: test_%.sv
	$(VCS) $(OPTS) $< \
	       +define+OC_ETHERNET_BUG $(TB) $(DUT) $(SVA_CHECKER)
