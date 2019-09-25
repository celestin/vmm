// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
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


`include "timescale.v"

`include "wb_if.sv"
`include "mii_if.sv"

program test;

`define MII_MAC_BFM__SV
`include "../tb_env.sv"

// Example 5-38
class my_dut_eth_frame extends dut_eth_frame;
   rand bit match;

   constraint match_dut_address {
      match dist {1:/9, 0:/1};
      if (match) dst == cfg.dut_addr;
      else       dst != cfg.dut_addr;
   }

   function new(test_cfg cfg);
      super.new(cfg);
   endfunction: new
endclass: my_dut_eth_frame


initial
begin
   tb_env env = new;

   env.gen_cfg();
   env.cfg.run_for_n_rx_frames = 0;
   env.build();
   begin
      my_dut_eth_frame fr = new(env.cfg);
      env.phy_src.randomized_obj = fr;
   end
   env.run();
end
endprogram: test
