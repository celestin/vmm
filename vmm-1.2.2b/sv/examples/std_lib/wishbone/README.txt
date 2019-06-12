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


			 Wishbone VIP Example


To run the VIP-only test:

   % make
   ...
   Simulation PASSED on /./ (/./) at 12920ns (0 warnings, 0 demoted errors & 0 demoted warnings)
   $finish at simulation time 12920ns



The example test has the following structure:

 100 read & write <-> Wishbone <-> Wishbone  <-> Wishbone ->   RAM
                       Master      Interface      Slave   <- Response



Files:

	config.sv		Configuration Descriptor
	cycle.sv		Transaction Descriptor
	master.sv		Master Transactor
	master_chk.sv		Master Protocol Checker
	slave.sv		Slave Transactor
	slave_chk.sv		Slave Protocol Checker
	test.sv			VIP-only Test
	wb_chk_coverage.sv	Protocol Checker Coverage Model
	wb_if.sv		Interface Declaration
	wishbone.sv		Top-level VIP file
