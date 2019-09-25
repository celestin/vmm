//
// -------------------------------------------------------------
//    Copyright 2004-2009 Synopsys, Inc.
//    All Rights Reserved Worldwide
//
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//





program cntrlr_tb;
  `include "vmm.sv"
  `include "cntrlr_env.sv"
  `include "test_random.sv"
  `include "test_write_back2back.sv"
  `include "test_read_back2back.sv"
  `include "test_write_read_same_addr.sv"
  `include "test_directed.sv"
  `include "test_error.sv"	
  `include "test_concatenate1.sv"
  `include "test_concatenate2.sv"

//Environment
cntrlr_env                      env;

//Ports for connection with DUT
cpuport                         cpu_port;
sramport                        sram_port0;
sramport                        sram_port1;
sramport                        sram_port2;
sramport                        sram_port3;

//Configuration of RTL
cntrlr_config                   cntrlr_cfg;
vmm_rtl_config_default_file_format dflt_fmt;

initial begin
   env = new("env");
   cpu_port = new("cpu_port",test_top.cpuif);
   sram_port0 = new("sram_port", test_top.sramif0);
   sram_port1 = new("sram_port", test_top.sramif1);
   sram_port2 = new("sram_port", test_top.sramif2);
   sram_port3 = new("sram_port", test_top.sramif3);

   cntrlr_cfg = new("cntrlr_cfg");

   vmm_opts::set_object("CPU:CPUDrv:cpu_port",cpu_port, env);
   vmm_opts::set_object("SRAM:SRAM_0:sram_port",sram_port0, env);
   vmm_opts::set_object("SRAM:SRAM_1:sram_port",sram_port1, env);
   vmm_opts::set_object("SRAM:SRAM_2:sram_port",sram_port2, env);
   vmm_opts::set_object("SRAM:SRAM_3:sram_port",sram_port3, env);

   vmm_opts::set_object("@%*:cpu_cfg",cntrlr_cfg.cpu_cfg,env);
   vmm_opts::set_object("@%*:sram_cfg",cntrlr_cfg.sram_cfg,env);

   dflt_fmt = new();
   vmm_rtl_config::default_file_fmt = dflt_fmt;
   vmm_simulation::list();
   vmm_simulation::run_tests();
end


endprogram
