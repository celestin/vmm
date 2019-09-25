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

// Example 5-24
constraint eth_frame::test_constraints1 {
`ifndef NO_SIZE_IN_CONSTRAINT
   data.size() == min_len;
`endif
}


program test_directed;

`include "../tb_env.sv"

class my_env  extends tb_env;

  function void gen_cfg();
   super.gen_cfg();
   cfg.run_for_n_tx_frames = 99;
   cfg.run_for_n_rx_frames = 99;
   cfg.mac.promiscuous = 1;
  endfunction

  task start();
   super.start();
   host_src.stop_xactor();
   phy_src.stop_xactor();
  endtask

endclass

my_env env = new;

initial
begin

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
   void'(to_phy.randomize());
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
