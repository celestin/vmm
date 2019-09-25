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

program test_sequences;

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


`ifdef USE_VMM_ENV_SUBTYPE

// A better way to customize the env for directed testing?
// prevents manual stepping through phases in the initial
// block, which is not scalable. What if this env were to
// become a subenv of a larger testbench? Out-of-module
// hierarchical references are also a serious barrier to
// reuse. (See tb_top.iii.tx_clk references above.)

class my_env  extends tb_env;

  eth_frame_sequence_gen alt_phy_src;

  function void gen_cfg();
   super.gen_cfg();
   cfg.run_for_n_tx_frames = 0;
   cfg.mac.promiscuous = 1;
  endfunction

  function void build();
    my_scenarios seq;
    seq = new;
    super.build();
    phy.log.set_verbosity(vmm_log::TRACE_SEV );
    alt_phy_src = new("PHY Side", 1, phy_src.out_chan);
    alt_phy_src.randomized_sequence = seq;
  endfunction

  task start();
   super.start();
   phy_src.reset_xactor();
   alt_phy_src.start_xactor();
   ovm_top.print_topology();
  endtask

endclass

my_env env = new;

initial
  env.run(); // just do it; no single-stepping

`else

tb_env env = new;

initial
begin
   eth_frame_sequence_gen phy_src;
   my_scenarios seq;
   
   seq = new;

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

`endif // OVM
endprogram
