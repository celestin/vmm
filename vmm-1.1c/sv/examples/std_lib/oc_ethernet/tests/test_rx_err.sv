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

program test_rx_err;

`include "../tb_env.sv"

tb_env env = new;

class mii_rx_err;
   rand int on_symbol;
  
   eth_frame    frame;
   int unsigned n_symbols;

   constraint mii_rx_err_valid {
      on_symbol >= -1;
      on_symbol < n_symbols;
   }

   constraint interesting_distribution {
      on_symbol dist {-1 :/ 1, [0:n_symbols] :/ 2};
   }
endclass: mii_rx_err


// Example 5-19
class gen_rx_errs extends mii_phy_layer_callbacks;
   mii_rx_err randomized_rx_err;

   function new();
      this.randomized_rx_err = new;
   endfunction: new

   virtual task pre_frame_tx(mii_phy_layer   xactor,
                             /*const*/ eth_frame frame,
                             mii_phy_collision col,
                             ref logic [7:0] bytes[]);
      this.randomized_rx_err.frame = frame;
      this.randomized_rx_err.n_symbols = (bytes.size() + 8) * 2;
      if (!this.randomized_rx_err.randomize()) begin
         `vmm_fatal(xactor.log, "Unable to randomize for an RX_ER injection");
         this.randomized_rx_err.on_symbol = -1;
      end
   endtask

   virtual task pre_symbol_tx(mii_phy_layer         xactor,
                              /*const*/ eth_frame       frame,
                              /*const*/ ref logic [7:0] bytes[],
                              /*const*/ input int       nibble_no,
                              ref logic [3:0]       symbol,
                              ref logic             dv,
                              ref logic             err,
                              ref bit               drop);
      if (this.randomized_rx_err.on_symbol == nibble_no) begin
         err = 1'b1;
         `vmm_note(xactor.log, $psprintf("Asserting Rx_ER on symbol #%0d...",
                                         this.randomized_rx_err.on_symbol));
         // Example 5-56
         env.sb.rx_err = 1;
      end
   endtask

endclass: gen_rx_errs


initial
begin
   env.gen_cfg();

   env.cfg.run_for_n_tx_frames = 0;

   // Example 5-57
   env.build();

   begin
      gen_rx_errs cb;
      cb = new;
      env.phy.prepend_callback(cb);
   end

`ifdef OC_ETHERNET_BUG
   void'(env.sb.log.modify(.text("/Unexpected frame received on MAC side/"),
                     .new_severity(vmm_log::WARNING_SEV)));
`endif

   env.run();
end
endprogram: test_rx_err
