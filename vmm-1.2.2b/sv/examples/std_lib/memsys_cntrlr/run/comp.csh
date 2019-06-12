#!/bin/csh -f

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

vcs   -sverilog +define+VMM_12 -debug_all -lca -ntb_opts rvm +vcs+lic+wait -parameters param.txt ../hdl/cntrlr.v +incdir+../cntrlr_env+../tests+../hdl+../vips/sram+../vips/cpu ../cntrlr_env/cntrlr_test_top.sv ../cntrlr_env/cntrlr_tb.sv -l comp.log
