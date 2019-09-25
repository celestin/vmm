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

// Example 5-34
class my_scenarios extends eth_frame_sequence;

   int TURN_RX_ON_IN_MIDDLE = define_sequence("Turn Rx ON in middle of frame", 5);

   constraint turn_rx_on_in_middle {
      if (sequence_kind == TURN_RX_ON_IN_MIDDLE) {
         length == 5;
      }
   }

   virtual task apply(eth_frame_channel channel,
                      ref int           n_insts);
      if (this.sequence_kind == this.TURN_RX_ON_IN_MIDDLE) begin
         wb_cycle cyc = new(env.cfg.wb);
         bit [31:0] val;
         bit ok;

         // Example 5-34
         // Make sure frames are first received OK
         channel.put(this.items[0]);
         channel.put(this.items[1]);

         // Make sure the frame has been received
         repeat (100) @ (posedge tb_top.mii.tx_clk);

         // Turn off Tx and Rx paths
         `vmm_note(env.log, "Turning TX & Rx OFF...");
         ok = cyc.randomize() with {kind == wb_cycle::READ;
                                    addr == 32'h0000_0000;
                                    sel  == 4'hF;};
         if (!ok) begin
            `vmm_fatal(env.log, "Unable to create READ cycle to MODER");
         end
         // Example 5-34
         env.host.exec_chan.put(cyc);
         if (cyc.status !== wb_cycle::ACK) begin
            `vmm_error(env.log, "Unable to read from MODER");
         end
         val = cyc.data;
         val[1:0] = 2'b00;
         ok = cyc.randomize() with {kind == wb_cycle::WRITE;
                                    addr == 32'h0000_0000;
                                    data == val;
                                    sel  == 4'hF;};
         if (!ok) begin
            `vmm_fatal(env.log, "Unable to create WRITE cycle to MODER");
         end
         env.host.exec_chan.put(cyc);
         if (cyc.status !== wb_cycle::ACK) begin
            `vmm_error(env.log, "Unable to write to MODER");
         end

         // Wait for the interface to be idle for a while
         `vmm_note(env.log, "Waiting for MII interface to go idle...");
         begin: wait_for_mii_if_idle
            repeat (3) begin: mii_if_not_idle
               wait (tb_top.mii.crs === 1'b0);
               fork
                  @ (posedge tb_top.mii.crs) disable mii_if_not_idle;
               join_none
               repeat (100) @ (posedge tb_top.mii.tx_clk);
               disable wait_for_mii_if_idle;
            end
            `vmm_fatal(env.log, "MII interface refuses to go idle");
         end

         `vmm_note(env.log, "Turning RX path ON in middle of next frame...");
         // Example 5-34
         fork
            channel.put(this.items[2]);
         join_none

         // Wait after the SDF, then turn on the Rx path
         @ (posedge tb_top.mii.crs);
         env.sb.rx_err = 1;
         repeat (8) @ (posedge tb_top.mii.tx_clk);
         val[1:0] = 2'b01;
         ok = cyc.randomize() with {kind == wb_cycle::WRITE;
                                    addr == 32'h0000_0000;
                                    data == val;
                                    sel  == 4'hF;};
         if (!ok) begin
            `vmm_fatal(env.log, "Unable to create WRITE cycle to MODER");
         end
         // Example 5-34
         env.host.exec_chan.put(cyc);
         if (cyc.status !== wb_cycle::ACK) begin
            `vmm_error(env.log, "Unable to write to MODER");
         end

         // Make sure subsequent frames are received OK
         `vmm_note(env.log, "Making sure subsequent frames are received OK...");
         channel.put(this.items[3]);
         channel.put(this.items[4]);
         
         // Turn Tx back on after we are done
         val[1:0] = 2'b11;
         ok = cyc.randomize() with {kind == wb_cycle::WRITE;
                                    addr == 32'h0000_0000;
                                    data == val;
                                    sel  == 4'hF;};
         if (!ok) begin
            `vmm_fatal(env.log, "Unable to create WRITE cycle to MODER");
         end
         env.host.exec_chan.put(cyc);
         if (cyc.status !== wb_cycle::ACK) begin
            `vmm_error(env.log, "Unable to write to MODER");
         end

         n_insts = 4;

         return;
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
   env.cfg.run_for_n_rx_frames = 4;
   env.cfg.mac.promiscuous = 1;

   env.build();
   env.phy.log.set_verbosity(vmm_log::TRACE_SEV );

   // Replace the PHY-side atomic generator with a scenario generator
   phy_src = new("PHY Side", 1, env.phy_src.out_chan);
   phy_src.randomized_sequence = seq;

   env.start();
   env.phy_src.reset_xactor();
   phy_src.start_xactor();

   env.run();
end
endprogram: test
