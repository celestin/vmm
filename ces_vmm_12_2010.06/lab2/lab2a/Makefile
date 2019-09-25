HOME     = ../../..
VIP_HOME  	= $(HOME)/vips
RTL_CFG  	= $(HOME)/RTL_CFG
VCS  		= vcs
#WHH
ifndef VMM_HOME 
	OPT  		= -sverilog -debug_all -ntb_opts rvm +vcs+lic+wait +define+VMM_12
else
	OPT  		= -sverilog -debug_all +incdir+$(VMM_HOME)/sv +vcs+lic+wait +define+VMM_12
endif
INC  		= +incdir+$(HOME)/cntrlr_env+$(HOME)/hdl+$(VIP_HOME)/sram+$(VIP_HOME)/cpu+$(HOME)/run
TEST 		= test_random
SCEN_CNT 		= 5
WAVE_OPT = 
PERF_OPT = /tools/synopsys/vcs.2009.06/vcs/etc/rvm/shared/src/vmm_sql_sys_info.c
PLAYBACK_EN = OFF
LOG = NORMAL
SEED = 1
ifeq ($(PLAYBACK_EN), ON)
PLAYBACK = playback
endif


ifeq ($(WAVE_EN), ON)
WAVE_OPT   = +define+ENABLE_WAVE 
endif

default: comp run

clean:
	rm -rf *simv* csrc *.vpd *.tcl  work/* core* ucli.key *.svshell vc_hdrs*\
  .vcsmx_rebuild *.cm *.daidir *.log *.db 

comp:
	$(VCS) $(OPT) $(INC) $(WAVE_OPT) ./hdl/cntrlr.v \
	./cntrlr_test_top.sv cntrlr_tb.sv 


run:
	./simv +ntb_random_seed=$(SEED) -l run.log +vmm_log_default=$(LOG)

gen_rtl_cfg:
	./simv +vmm_rtl_config=$(RTL_CFG) +ntb_random_seed=$(SEED) +vmm_gen_rtl_config -l $(TEST).log +vmm_test=$(TEST)
	./cfg2param.pl ../RTL_CFG/cntrlr_cfg/sram_cfg.cfg
    
	
test_%:
	./simv +vmm_rtl_config=$(RTL_CFG) +ntb_random_seed=$(SEED)  -l $@.log +vmm_test=$@

test_concat:
	./simv +vmm_rtl_config=$(RTL_CFG) +ntb_random_seed=$(SEED)  -l $@.log +vmm_test=test_concatenate1+test_concatenate2

nuke: clean
	rm *.sv
	rm -rf solutions hdl
	cp -r .orig/* .

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
	@echo "################################################################"

