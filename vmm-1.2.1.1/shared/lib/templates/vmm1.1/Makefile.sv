#
# Template for Makefile
# <VNAME>      Name of VIP
# <MOD>        Name of top module
# <PB>         Name of program block
# [filename]   Makefile

################################################################################
PROJECT_NAME = VNAME
################################################################################

INCL      = +incdir+../include+../src+../env+../tests+../hdl

# +define+VMM_PARAM_CHANNEL   Used for parameterized class/channel
# +define+VMM_SB_DS_IN_STDLIB Used for scoreboard inbuilt method
DEFINES   = +define+VMM_LOG_FORMAT_FILE_LINE +define+VMM_PARAM_CHANNEL +define+VMM_SB_DS_IN_STDLIB 
RUN_OPTS  =
TEST = TEST_NAME 
# ToDo: Top level dut file
DUT =  
NUM_TRANS = 1 # Number of transaction count. Default set to 1
SEED      = 1 # Default seed set to 1
VERBOSITY = debug
MODE      = NORMAL # Default configuration record-replay mode set to NORMAL
#### VCS and VMM checking
ifdef VCS_HOME
 ifndef VMM_HOME
  VMM = -ntb_opts rvm
  PERF_START
  PERF_OPT = $(VCS_HOME)/etc/rvm/shared/src/vmm_sql_sys_info.c
  PERF_END
 else
  VMM = +incdir+$(VMM_HOME)/sv+$(VMM_HOME)/sv/sb
  PERF_START
  PERF_OPT = $(VMM_HOME)/shared/src/vmm_sql_sys_info.c
  VMM_PERF_FILE= $(VMM_HOME)/sv/vmm_perf.sv
  PERF_END
 endif
else
 ERR_STATUS = 1
endif

COMP_OPTS =  -sverilog $(VMM) $(INCL) $(DEFINES)

all default: check clean comp run 

check:
ifdef ERR_STATUS
	@echo ""
	@echo "ERROR : VCS_HOME is not set"
	@echo "Please set VCS_HOME to run this Makefile"
	@echo ""
endif

comp: check
ifndef ERR_STATUS
RAL_START
	cd ../env; ralgen -l sv -t VNAME -c b -c a -c f VNAME.ralf;cd -
RAL_END
	vcs $(COMP_OPTS) $(VMM_OBJ_DEF_1) $(VMM_OBJ_DEF_2) $(PERF_OPT) \
        $(VMM_PERF_FILE) ../tests/PB.sv ../hdl/MOD.sv 
endif

run: check
ifndef ERR_STATUS
	./simv +vmm_opts+$(NUM_TRANS) +vmm_MODE=$(MODE) $(RUN_OPTS) +vmm_test=$(TEST) \
        +ntb_random_seed=$(SEED) +vmm_force_verbosity=$(VERBOSITY)
endif

clean:
	rm -rf simv* csrc
	rm -rf vc_hdrs.h .vcsmx_rebuild *.log
	rm -rf work/* *.svshell

help:
	@echo "****************************************************************"
	@echo "***   Makefile Help for VNAME VIP :  *** " 
	@echo "****************************************************************"
	@echo "*  Usage:                                                      *"
	@echo "*  ------                                                      *"
	@echo "*  make       Compile and Run the testcase                     *"
	@echo "*                                                              *"
	@echo "*  Available targets:                                          *"
	@echo "*  make help  [To see the Help]                                *"
	@echo "*  make clean [Remove simulation generated files/directories]  *"
	@echo "*  make comp  [Compile the testcase]                           *"
	@echo "*  make run   [Run the testcase]                               *"
	@echo "*                                                              *"
	@echo "*  Optional Arguments                                          *"
	@echo "*  NUM_TRANS         [To run the testcase for n transaction]   *"
	@echo "*  make NUM_TRANS=n  [example make NUM_TRANS=3 ]               *"
	@echo "*  VERBOSITY         [Message severity to be display]          *"
	@echo "*  make VERBOSITY=<sev> [example make VERBOSITY=note]          *"
	@echo "*  MODE              [Record replay mechanism mode]            *"
	@echo "*  make MODE=<mode>  [example make MODE=RECORD]                *"
	@echo "****************************************************************"


