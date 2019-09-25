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



HOME     = ..
VIP_HOME  	= $(HOME)/vips
RTL_CFG  	= $(HOME)/RTL_CFG
VCS  		= vcs
OPT  		= -sverilog +define+VMM_12 -debug_all -lca -ntb_opts rvm +vcs+lic+wait -parameters param.txt
INC  		= +incdir+$(HOME)/cntrlr_env+$(HOME)/tests+$(HOME)/hdl+$(VIP_HOME)/sram+$(VIP_HOME)/cpu
TEST 		= test_random
SCEN_CNT 		= 5
WAVE_OPT = 
MODE = NORMAL


ifeq ($(WAVE_EN), ON)
WAVE_OPT   = +define+ENABLE_WAVE 
endif

default: comp run

clean:
	rm -rf *simv* csrc *.vpd *.tcl  work core* *.dat ucli.key *.svshell vc_hdrs*\
  .vcsmx_rebuild *.cm *.daidir *.log *.db 

comp:
	$(VCS) $(OPT) $(INC) $(WAVE_OPT) $(HOME)/hdl/cntrlr.v \
	$(HOME)/cntrlr_env/cntrlr_test_top.sv $(HOME)/cntrlr_env/cntrlr_tb.sv 


run:
	./simv +vmm_rtl_config=$(RTL_CFG) -l $(TEST).log +vmm_test=$(TEST)

gen_rtl_cfg:
	./simv +vmm_rtl_config=$(RTL_CFG) +vmm_gen_rtl_config -l $(TEST).log +vmm_test=$(TEST)
	./cfg2param.pl ../RTL_CFG/cntrlr_cfg/sram_cfg.cfg
    
	
test_%:
	./simv +vmm_rtl_config=$(RTL_CFG) -l $@.log +vmm_test=$@ +vmm_opts+MODE=$(MODE)

test_concat:
	./simv +vmm_rtl_config=$(RTL_CFG) -l $@.log +vmm_test=test_concatenate1+test_concatenate2

all:   comp gen_rtl_cfg  test_random test_directed test_read_back2back test_write_back2back test_write_read_same_addr test_error test_concat 
	

help:
	@echo "################################################################"
	@echo "TO CLEAN :                                                      "
	@echo "make clean                                                      "
	@echo "                                                                "
	@echo "TO COMPILE :                                                    "
	@echo "make comp                                                       "
	@echo "                                                                "
	@echo "TO RUN TEST:                                                    "
	@echo "make <testcase name>                                            "
	@echo "EXAMPLE:                                                        "
	@echo "make test_random                                                "
	@echo "                                                                "
	@echo "TO RECORD TEST:                                                 "
	@echo "make <testcase name> MODE=RECORD                                "
	@echo "                                                                "
	@echo "TO PLAYBACK TEST:                                               "
	@echo "make <testcase name> MODE=PLAYBACK                              "
	@echo "################################################################"

