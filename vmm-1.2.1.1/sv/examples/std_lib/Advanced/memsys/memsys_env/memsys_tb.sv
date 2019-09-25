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

program memsys_tb;
  `include "vmm.sv"
  `include "memsys_env.sv"
  `include "test1.sv"
  `include "test2.sv"
  `include "test_write.sv"

memsys_env                      env;
cpuport                         cpu_port0;
cpuport                         cpu_port1;

initial begin
   env = new("env");
   cpu_port0 = new("cpuport0",test_top.port0);
   cpu_port1 = new("cpuport1",test_top.port1);
   vmm_opts::set_object("CPU0:Drv:cpu_port",cpu_port0, env);
   vmm_opts::set_object("CPU1:Drv:cpu_port",cpu_port1, env);

   vmm_simulation::list();
   vmm_simulation::run_tests();
end


endprogram
