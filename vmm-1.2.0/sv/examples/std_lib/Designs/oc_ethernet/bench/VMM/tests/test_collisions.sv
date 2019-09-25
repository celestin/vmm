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

program test_collisions;

`define MII_MAC_BFM__SV
`include "../tb_env.sv"

// Example 5-26
class must_be_half_duplex extends test_cfg;
   constraint hd {
      mii.full_duplex == 0;
   }
endclass


// Example 4-44
// Example 5-25
class long_eth_frame extends eth_frame;
   constraint long_frames {
      data.size() == max_len;
   }
endclass: long_eth_frame


class ifg_if_no_col extends mii_phy_layer_callbacks;
   virtual task pre_frame_tx(mii_phy_layer   xactor,
                             /*const*/ eth_frame frame,
                             mii_phy_collision col,
                             ref logic [7:0] bytes[]);
      if (col.kind == mii_phy_collision::NONE) begin
         // Poor man's IFG
         @ (negedge xactor.sigs.crs);
         repeat (10) @ (xactor.sigs.prx);
         env.sb.sent_from_phy_side(frame);
      end
   endtask
endclass


initial
begin
   tb_env env = new;

   // Example 5-26
   begin
      must_be_half_duplex cfg = new;
      env.cfg = cfg;
   end

   env.gen_cfg();
   // env.cfg.run_for_n_rx_frames = 3;
   env.cfg.run_for_n_tx_frames = env.cfg.run_for_n_rx_frames * 2;

   env.build();

   // Example 5-25
   // MAC->PHY will transmit long frames for max collision range
   begin
      long_eth_frame fr = new;
      env.host_src.randomized_obj = fr;
   end

   // By-pass the MAC layer on the PHY side to avoid back-offs and deference
   // and be able to inject collisions at every frame transmitted by
   // the MAC side.

   env.phy_src.out_chan = env.phy.tx_chan;

   // Minimal IFG on the PHY side if no collisions
   begin
      ifg_if_no_col cb = new;
      env.phy.prepend_callback(cb);
   end

   // Example 5-17
   // Example 5-23
   env.phy.randomized_col.no_collision.constraint_mode(0);

   // Stop the simulation when PHY-side generator is done
   fork
      begin
         env.phy_src.notify.wait_for(eth_frame_atomic_gen::DONE);
         ->env.end_test;
      end
   join_none

   env.phy.log.set_verbosity(vmm_log::TRACE_SEV );

   // Transmission errors are to be expected
   env.swem.log.modify(.text("An error occured during the transmission of a frame"),
                       .new_severity(vmm_log::WARNING_SEV));

   env.run();
end
endprogram: test_collisions
