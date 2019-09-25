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


program test_directed;

`define MII_MAC_BFM__SV
`include "../tb_env.sv"

// Example 5-24
constraint eth_frame::test_constraints1 {
`ifndef NO_SIZE_IN_CONSTRAINT
   data.size() == min_len;
`endif
}

initial
begin
   tb_env env = new;

   env.gen_cfg();
   env.cfg.run_for_n_tx_frames = 99;
   env.cfg.run_for_n_rx_frames = 99;
   env.cfg.mac.promiscuous = 1;
   // Example 5-11
   env.start();
   env.host_src.stop_xactor();
   env.phy_src.stop_xactor();

   fork
      directed_stimulus;
   join_none

   env.run();
end

task directed_stimulus;
   eth_frame to_phy, to_mac;
   bit dropped;

   repeat (100) @(negedge tb_top.tx_clk);

   // Example 5-13
   to_phy = new;
   to_phy.randomize();
   $cast(to_mac, to_phy.copy());

   fork
      env.host_src.inject(to_phy, dropped);
      begin
         // Force a collision
         @ (posedge tb_top.mii.tx_en);
         env.phy_src.inject(to_mac, dropped);
      end
   join

   repeat (1000) @(negedge tb_top.tx_clk);

   -> env.end_test;
endtask: directed_stimulus
endprogram: test_directed
