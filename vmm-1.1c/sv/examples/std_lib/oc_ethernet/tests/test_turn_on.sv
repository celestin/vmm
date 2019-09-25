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
// 


`include "timescale.v"


`include "wishbone.sv"
`include "mii.sv"


program test_turn_on;


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
         `vmm_note(env.log, "Turning RX path ON right NOW...");
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

         // Make sure the frame has been received
         repeat (100) @ (posedge tb_top.mii.tx_clk);

         if (env.cfg.run_for_n_rx_frames != 0) begin
           `vmm_error(this.log,
              $psprintf("Scoreboard did not see the expected number of frames."));
           -> env.end_test;
         end

         n_insts = 5;

      end

   endtask: apply
endclass: my_scenarios


`include "../tb_env.sv"

`ifdef OVM

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
   cfg.run_for_n_rx_frames = 5;
   cfg.mac.promiscuous = 1;

   cfg.n_tx_bd = 4; // tb not robust against # descriptors 
   cfg.n_rx_bd = 2; //  and other things
  endfunction

  function void build();
    my_scenarios seq;
    super.build();
    phy.log.set_verbosity(vmm_log::TRACE_SEV );
    alt_phy_src = new("PHY Side", 1, phy_src.out_chan);
    seq = new;
    alt_phy_src.randomized_sequence = seq;
  endfunction

  task start();
   super.start();
   phy_src.reset_xactor();
   alt_phy_src.start_xactor();
   ovm_top.print_topology();

   // The tb_env assumes RxBDs are used in consecutive order. Apparently, if
   // you disable then reenable the Rx side, this is not the case. The spec
   // says nothing, meaning no assumptions about which descriptor should be made.
   void'(swem.log.modify(.text("No received RxBD were found"),
                       .new_severity(vmm_log::WARNING_SEV)));

  endtask

endclass

my_env env = new;

initial
  env.run();

`else

tb_env env = new;

initial
begin
   /* Not really a good way to customize env; simply extend tb_env as above */
   

   eth_frame_sequence_gen phy_src;
   my_scenarios seq;
   
   seq = new;

   env.gen_cfg();

   env.cfg.run_for_n_tx_frames = 0;
   env.cfg.run_for_n_rx_frames = 5;
   env.cfg.mac.promiscuous = 1;

   env.build();

   env.phy.log.set_verbosity(vmm_log::TRACE_SEV );

   // Replace the PHY-side atomic generator with a scenario generator
   phy_src = new("PHY Side", 1, env.phy_src.out_chan);
   phy_src.randomized_sequence = seq;
   phy_src.stop_after_n_insts = 5;

   env.start();
   env.phy_src.reset_xactor();
   phy_src.start_xactor();

   void'(env.swem.log.modify(.text("No received RxBD were found"),
                       .new_severity(vmm_log::WARNING_SEV)));
   env.run();
end

`endif // OVM

endprogram: test_turn_on
