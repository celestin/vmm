//
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    Copyright 2008-2009 Mentor Graphics Corporation
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
// This file was modified by Mentor Graphics. See QUESTA.html
// in root directory for details.

`include "timescale.v"

`include "wishbone.sv"
`include "mii.sv"

program test_bad_dst;

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

tb_env env = new;

initial
begin
   my_dut_eth_frame fr;
   env.gen_cfg();
   env.cfg.mac.promiscuous = 0;
   env.cfg.run_for_n_tx_frames = 0;
   env.build();
   env.cfg_dut();
   fr = new(env.cfg);
   env.phy_src.randomized_obj = fr;
   env.run();
end
endprogram
