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


APB	= ../apb

VCS	= vcs -R +plusarg_save -sverilog -ntb_opts dtm \
              +incdir+$(VMM_HOME)/sv+$(APB) +vmm_log_default=trace

all: simple annotate

simple test_simple:
	$(VCS) test_simple.sv tb_top.sv

random test_random:
	$(VCS) +define+RANDOM_RESPONSE test_simple.sv tb_top.sv

annotate test_annotate:
	$(VCS) test_annotate.sv tb_top.sv

clean:
	rm -rf csrc simv* vc_hdrs.h *~ apb/*~
