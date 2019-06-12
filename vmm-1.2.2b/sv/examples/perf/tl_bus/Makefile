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

OPTS	=

VCS	= vcs -R -sverilog -ntb_opts dtm \
	      +incdir+$(VMM_HOME)/sv $(OPTS) 

all test: sqlite sqltxt

sqlite:
ifeq ($(SQLITE3_HOME),)
	echo "ERROR: Please set environment variable SQLITE3_HOME for running this example."
	exit 1
endif
	$(VCS) +define+USE_SQLITE test.sv \
	       $(VMM_HOME)/shared/src/vmm_sqlite_interface.c \
	       -CFLAGS "-I$(SQLITE3_HOME)/include"

sqltxt:
	$(VCS) +define+USE_SQLTXT test.sv \
	       $(VMM_HOME)/shared/src/vmm_sqltxt_interface.c

clean:
	rm -rf simv* csrc *~ *.db *.log *.sql vc_hdrs.h
