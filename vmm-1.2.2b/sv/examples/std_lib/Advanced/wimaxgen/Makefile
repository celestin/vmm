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

ifdef VMM_HOME
OPTS = +define+VMM_12 +incdir+$(VMM_HOME)/sv
else
OPTS = +define+VMM_12 -ntb_opts rvm
endif

all: comp run

comp:
	vcs -sverilog top.sv -timescale="1ns/1ps" -debug_all $(OPTS)

clean:
	rm -rf vcdplus.vpd  simv* csrc vc_hdrs.h  .vcsmx_rebuild
	rm -rf gen.dat bad_log

run:
	./simv +vmm_test=test1+test2 +vmm_opts+num_of_dl_pusc_subchannels=28@%phy_cfg_inst_string_name -l run.log
