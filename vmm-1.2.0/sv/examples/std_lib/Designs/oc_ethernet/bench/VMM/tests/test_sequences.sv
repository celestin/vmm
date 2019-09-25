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

// Example 5-30
class my_scenarios extends eth_frame_sequence;

   // Example 5-31
   int SHORT_FRAMES = define_sequence("Burst of short frames", 10);
   int REPEAT_10    = define_sequence("Repeat 10x", 1);
   int BACK_OFF     = define_sequence("Back-off", 1);

   // Example 5-30
   // Example 5-32
   constraint burst_of_short_frames {
      if (sequence_kind == SHORT_FRAMES) {
         length > 2;
`ifndef NO_FOREACH_CONSTRAINT
         foreach (items[i]) {
            items[i].data.size() == items[i].min_len;
         }
`endif
      }
   }

   // Example 5-33
   constraint repeat_10_frames {
      if (sequence_kind == REPEAT_10) length == 1;
   }

   constraint back_off {
      if (sequence_kind == BACK_OFF) length == 1;
   }

   virtual function string psdisplay(string prefix = "");
      psdisplay = super.psdisplay(prefix);
   endfunction:psdisplay

   // Example 5-30
   // Example 5-33
   virtual task apply(eth_frame_channel channel,
                      ref int           n_insts);
      if (this.sequence_kind == this.REPEAT_10) begin
         int i = 0;
         repeat (10) begin
            eth_frame fr;
            $cast(fr, this.items[0].copy());
            fr.data_id = i++;
            channel.put(fr);
         end
         n_insts = 10;
         return;
      end

      if (this.sequence_kind == this.BACK_OFF) begin
         fork
            begin
               eth_frame fr;
               bit drop;
               $cast(fr, this.items[0].copy());
               env.host_src.inject(fr, drop);
            end
         join_none
         @ (posedge tb_top.mii.crs);
      end

      super.apply(channel, n_insts);
   endtask: apply
endclass: my_scenarios

initial
begin
   tb_env env = new;

   eth_frame_sequence_gen phy_src;
   my_scenarios seq = new;

   env.gen_cfg();
   env.cfg.run_for_n_tx_frames = 0;
   env.cfg.mac.promiscuous = 1;

   env.build();

   // Replace the PHY-side atomic generator with a scenario generator
   phy_src = new("PHY Side", 1, env.phy_src.out_chan);
   phy_src.randomized_sequence = seq;

   env.start();
   env.phy_src.reset_xactor();
   phy_src.start_xactor();

   env.run();
end
endprogram: test
