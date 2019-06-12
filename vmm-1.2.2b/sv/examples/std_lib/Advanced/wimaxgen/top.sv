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

`define VMM_12


program P;
`include "vmm.sv"
`include "phy_env.sv"
`include "test1.sv"
`include "test2.sv"

   // external constraints are shared across tests
   constraint phy_tb_config::cst_user {
      num_of_frames == 1;
   }

   test1 t1;
   test2 t2;

   initial begin
      phy_env env;
      env = new("env");
      t1 = new("test1");
      t2 = new("test2");
      vmm_simulation::run_tests();
   end
endprogram
