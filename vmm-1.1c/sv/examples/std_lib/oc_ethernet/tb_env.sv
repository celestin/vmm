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


class test_cfg;
   rand integer unsigned tx_rx_clk_offset;

   rand eth_mac_cfg mac;
   rand bit [47:0]  dut_addr;
   rand mii_cfg     mii;

   rand wb_slave_cfg  wb;

   rand bit [ 7:0] rx_bd_offset;
   rand bit [ 7:0] n_tx_bd;
   rand bit [ 7:0] n_rx_bd;
   rand bit [31:0] txrx_bfr_base;
        bit [31:0] txrx_pnt[*];

   rand bit [15:0] max_frame_len;
   rand bit        huge_enable;

   // Stop when both limits are reached
   rand integer unsigned run_for_n_tx_frames;
   rand integer unsigned run_for_n_rx_frames;
      
   constraint test_cfg_valid {
      tx_rx_clk_offset < 100;

      mac.rate inside {10, 100};
      mii.is_10Mb == (mac.rate == 10);
      mii.full_duplex == mac.full_duplex;

      dut_addr[47:46] == 2'b00;

      wb.port_size   == wb_cfg::DWORD;
      wb.granularity == wb_cfg::BYTE; 
      wb.cycles      == wb_cfg::CLASSIC;

      rx_bd_offset inside {[8'h01:8'h7F]};  // At least one TX BD and one Rx BD
      n_tx_bd > 0 && n_tx_bd < rx_bd_offset+1;
      n_rx_bd > 0 && n_rx_bd <= 'h80 - rx_bd_offset;

      txrx_bfr_base < 32'hFFFF_FFFF - 256 * ((huge_enable) ? 65536 : max_frame_len);
      txrx_bfr_base[2:0] == 3'b000;
   }

   // Example 6-10
   constraint coverage_driven {
      max_frame_len inside {1500, 1518, 'h0600};
   }

   constraint reasonable {
      run_for_n_tx_frames < 100;
      run_for_n_rx_frames < 100;
   }

   function new();
      this.mac = new;
      this.mii = new;
      this.wb  = new;
   endfunction: new

   function string psdisplay(string prefix = "");
      $sformat(psdisplay, "%sDUT MAC Addr: %h.%h.%h.%h.%h.%h", prefix,
               dut_addr[47:40], dut_addr[39:32], dut_addr[31:24], dut_addr[23:16], dut_addr[15:8], dut_addr[7:0]);
      $sformat(psdisplay, "%s\n%s", psdisplay, this.mac.psdisplay(prefix));
      $sformat(psdisplay, "%s\n%sTx/Rx Clock offset: %0d", psdisplay, prefix, this.tx_rx_clk_offset);
      $sformat(psdisplay, "%s\n%s", psdisplay, this.wb.psdisplay(prefix));
      $sformat(psdisplay, "%s\n%s%0d TxBD, #%0d RxBD based at 'h%h", psdisplay, prefix,
               this.n_tx_bd, this.n_rx_bd, this.txrx_bfr_base);
      $sformat(psdisplay, "%s\n%s%0d bytes max frame length", psdisplay, prefix,
               (this.huge_enable) ? 65536 : this.max_frame_len);
      $sformat(psdisplay, "%s\n%sfor %0d Tx + %0d Rx frames", psdisplay, prefix,
               this.run_for_n_tx_frames, this.run_for_n_rx_frames);
   endfunction
endclass: test_cfg


// Example 4-63
//
// Example of adding supplemental information to
// transaction descriptor received by a transactor
//
class annotated_eth_frame extends eth_frame;
   string direction = "Unknown";

   virtual function vmm_data allocate();
      annotated_eth_frame fr = new;
      allocate = fr;
   endfunction: allocate


   virtual function vmm_data copy(vmm_data to = null);
      annotated_eth_frame cpy;
      if (to == null) cpy = new;
      else if (!$cast(cpy, to)) begin
         //`vmm_fatal(to.log, "Unable to copy into non-annotated_eth_frame instance");
         $display("Error:Unable to copy into non-annotated_eth_frame instance");
         return null;
      end

      void'(super.copy(cpy));
      cpy.direction = this.direction;

      copy = cpy;
   endfunction: copy

   virtual function string psdisplay(string prefix = "");
      psdisplay = super.psdisplay({prefix, this.direction, ": "});
   endfunction: psdisplay

endclass: annotated_eth_frame


// Example 5-45
//
// Self-Checking Structure
//
class scoreboard;
   test_cfg cfg;
   vmm_log  log;

   eth_frame to_mac_side[$];
   eth_frame to_phy_side[$];

   // Example 5-56
   bit rx_err;

   local bit is_tx;
   local int frame_len;

   // Example 6-6
   `ifdef INCA
   covergroup frame_coverage;
   `else
   covergroup frame_coverage(test_cfg cfg);
   `endif
      direction: coverpoint is_tx {
         bins Tx = {1};
         bins Rx = {0};
         // Example 6-7
         option.weight = 0;
      } 
      hugen    : coverpoint cfg.huge_enable {
         option.weight = 0;
      }
      // Example 6-10
      max_fl   : coverpoint cfg.max_frame_len {
         bins fl_1500 = {1500};
         bins fl_1518 = {1518};
         bins fl_0600 = {'h0600};
         option.weight = 0;
      }
      // Example 6-2
      // Example 6-5
      `ifndef INCA
      frame_len: coverpoint frame_len {
         bins max_fl_less_4 = {cfg.max_frame_len - 4};
         bins max_fl_less_1 = {cfg.max_frame_len - 1};
         bins max_fl        = {cfg.max_frame_len};
         bins max_fl_plus_1 = {cfg.max_frame_len + 1};
         bins max_fl_plus_4 = {cfg.max_frame_len + 4};
         bins max_size      = {65535};
         option.weight = 0;
      }
      `endif
      // Example 6-3
      cross direction, hugen, max_fl, frame_len {
         // Example 6-9
         option.comment = "Coverage for Example 2-5";
      }
      // Example 6-8
      option.weight = 2 * 3 * 6;
   endgroup


   // Example 5-46
   function new(test_cfg cfg);
      this.cfg = cfg;
      this.log = new("Scoreboard", "");

      this.rx_err = 0;

      `ifdef INCA
      frame_coverage = new;
      `else
      frame_coverage = new(cfg);
      `endif
   endfunction: new

   // Example 5-48
   function void sent_from_mac_side(eth_frame fr);
      // Example 6-4
      this.is_tx     = 1;
      this.frame_len = fr.byte_size();
      this.frame_coverage.sample();

      // Is it too long?
      if (!this.cfg.huge_enable && fr.byte_size() > this.cfg.max_frame_len) return;

      // Will it be accepted by the PHY-side MAC layer?
      if (fr.fcs) return;// Not if it has a bad FCS

      if (!this.cfg.mac.promiscuous &&
          fr.dst !== this.cfg.mac.addr &&
          !fr.dst[47]) return; // Not if wrong unicast address

      to_phy_side.push_back(fr);
   endfunction

   function void sent_from_phy_side(eth_frame fr);
      // Example 6-4
      this.is_tx     = 0;
      this.frame_len = fr.byte_size();
      this.frame_coverage.sample();

      // Is it too long?
      if (!this.cfg.huge_enable && fr.byte_size() > this.cfg.max_frame_len) return;

      // Will it be accepted by the MAC-side MAC layer?
      if (fr.fcs) return;// Not if it has a bad FCS

      if (!this.cfg.mac.promiscuous &&
          fr.dst !== this.cfg.dut_addr) return; // Not if wrong unicast address

      to_mac_side.push_back(fr);
   endfunction

   // Example 5-48
   function void received_by_mac_side(eth_frame fr);
      eth_frame exp;
      string diff;

      if (this.cfg.run_for_n_rx_frames > 0) begin
         this.cfg.run_for_n_rx_frames--;
      end

      if (this.to_mac_side.size() == 0) begin
         `vmm_error(this.log, $psprintf("Unexpected frame received on MAC side (none expected):\n%s",
                                        fr.psdisplay("   ")));
         return;
      end

      exp = this.to_mac_side.pop_front();
      if (!fr.compare(exp, diff)) begin
         `vmm_error(this.log, $psprintf("Unexpected frame received on MAC side: %s:\n%s\n%s",
                                        diff, fr.psdisplay("   Actual: "),
                                        exp.psdisplay("   Expect: ")));
         return;
      end

      `vmm_note(this.log, $psprintf("Expected frame received on MAC side (%0d left):\n%s",
                                    this.cfg.run_for_n_rx_frames,
                                    fr.psdisplay("   ")));
   endfunction

   function void received_by_phy_side(eth_frame fr);
      eth_frame exp;
      string diff;

      if (this.cfg.run_for_n_tx_frames > 0) begin
         this.cfg.run_for_n_tx_frames--;
      end

      if (this.to_phy_side.size() == 0) begin
         `vmm_error(this.log, $psprintf("Unexpected frame received on PHY side (none expected):\n%s",
                                        fr.psdisplay("   ")));
         return;
      end

      exp = this.to_phy_side.pop_front();
      if (!fr.compare(exp, diff)) begin
         `vmm_error(this.log, $psprintf("Unexpected frame received on PHY side: %s:\n%s\n%s",
                                        diff, fr.psdisplay("   Actual: "),
                                        exp.psdisplay("   Expect: ")));
         return;
      end

      `vmm_note(this.log, $psprintf("Expected frame received on PHY side (%0d left):\n%s",
                                    this.cfg.run_for_n_tx_frames,
                                    fr.psdisplay("   ")));
   endfunction

endclass: scoreboard

// Example 5-53
class sb_mac_cbs extends eth_mac_callbacks;
   scoreboard sb;

   function new(scoreboard sb);
      this.sb = sb;
   endfunction

   virtual task post_frame_tx(eth_mac             xactor,
                              eth_frame           frame,
                              eth_frame_tx_status status);
      if (status.successful && !this.sb.rx_err) begin
         this.sb.sent_from_phy_side(frame);
      end
      else begin
         this.sb.cfg.run_for_n_rx_frames--;
      end
      this.sb.rx_err = 0;
   endtask
endclass



typedef class sw_emulator;
virtual class sw_emulator_callbacks extends vmm_xactor_callbacks;
   virtual task pre_frame_tx(sw_emulator   xactor,
                             ref eth_frame frame,
                             ref bit       drop);
   endtask

   virtual function void post_frame_rx(sw_emulator         xactor,
                                       /*const*/ eth_frame frame);
   endfunction
endclass: sw_emulator_callbacks


class sw_emulator extends vmm_xactor;

   eth_frame_channel tx_chan;
   scoreboard sb;

   local test_cfg  cfg;
   local wb_master host;
   local wb_ram    ram;

   local bit [31:0] avail_txbd[$];
   local bit [31:0] busy_txbd[$];
   bit [31:0] next_rxbd;
   local event avail_txbd_e;

   function new(string            inst,
                int unsigned      stream_id = -1,
                test_cfg          cfg,
                scoreboard        sb,
                wb_master         host,
                wb_ram            ram);
      super.new("SW Emulator", inst, stream_id);
      tx_chan = new("SW Emulator Tx Channel", inst);
      this.sb   = sb;
      this.cfg  = cfg;
      this.host = host;
      this.ram  = ram;

      this.reset_xactor();
   endfunction: new

   function void reset_xactor(reset_e rst_typ = SOFT_RST );
      super.reset_xactor(rst_typ);
      tx_chan.flush();
      this.host.reset_xactor(rst_typ);

      begin
         bit [31:0] bd_addr = 32'h0000_0400;
         repeat (this.cfg.n_tx_bd) begin
            this.avail_txbd.push_back(bd_addr);
            bd_addr += 8;
         end
         // Push a "wrap" flag
         this.avail_txbd.push_back(32'hFFFF_FFFF);
         -> this.avail_txbd_e;
      end
      `ifdef INCA
      this.busy_txbd.delete();
      `else
      this.busy_txbd = '{};
      `endif
   endfunction: reset_xactor

   virtual task main();
      fork
         super.main();
         this.tx_driver();
         this.int_serv();
      join
   endtask: main

   local task tx_driver();
      logic [ 7:0] bytes[];

      while (1) begin
         eth_frame fr;
         bit       drop = 0;
         bit       ok;

         // Wait for a free Tx buffer if none available
         while (this.avail_txbd.size() == 0) @(this.avail_txbd_e);
         
         this.wait_if_stopped_or_empty(this.tx_chan);
         this.tx_chan.activate(fr);

         `vmm_callback(sw_emulator_callbacks,
                       pre_frame_tx(this, fr, drop));

         if (!drop) begin
            bit   [31:0] bd_addr = this.avail_txbd.pop_front();
            bit   [31:0] tx_pnt = this.cfg.txrx_pnt[bd_addr];
            wb_cycle cyc = new(this.cfg.wb);
            bit        wrap = 0;

            void'(this.tx_chan.start());

            // Write the frame in the RAM
            // Example 4-27
            `vmm_trace(this.log, $psprintf("Buffering TX Frame at 'h%h:\n%s",
                                           tx_pnt, fr.psdisplay("   ")));
            
            // We need full DWORDs
            begin
               int len = fr.byte_size();
               bytes = new [len + (4 - len % 4)];
               void'(fr.byte_pack(bytes));
               for (int i = 0; i < len; i += 4) begin
                  this.ram.write(tx_pnt + i, {bytes[i], bytes[i+1], bytes[i+2], bytes[i+3]});
               end
            end

            // Set the TxBD accordingly
            if (this.avail_txbd.size() > 0) begin
               if (this.avail_txbd[0] == 32'hFFFF_FFFF) begin
                  wrap = 1;
                  void'(this.avail_txbd.pop_front());
               end
            end
            
            `vmm_debug(this.log, $psprintf("Updating TxBD at 'h%h",
                                           bd_addr));
            
            tx_pnt[31:16] = fr.byte_size();
            tx_pnt[15: 0] = 16'hD400;
            tx_pnt[13] = wrap;
            ok = cyc.randomize() with {kind == wb_cycle::WRITE;
                                       addr == bd_addr;
                                       data == tx_pnt;
                                       sel  == 4'hF;};
            if (!ok) begin
               `vmm_fatal(this.log, "Unable to create WRITE cycle to TxBD");
            end
            this.host.exec_chan.put(cyc);
            if (cyc.status !== wb_cycle::ACK) begin
               `vmm_error(this.log, "Unable to write to TxBD");
            end

            this.busy_txbd.push_back(bd_addr);
            if (wrap) this.busy_txbd.push_back(32'hFFFF_FFFF);

            void'(this.tx_chan.complete());

            this.sb.sent_from_mac_side(fr);
         end
         void'(this.tx_chan.remove());
      end
   endtask: tx_driver
      
   local task int_serv();
      wb_cycle cyc = new(this.cfg.wb);
      bit [31:0] isr;
      bit [31:0] val;
      bit        ok;

      bit ignore_fr;

      // Interrupt service routine
      while (1) begin
         wait(tb_top.wb_int === 1'b1);

         ignore_fr = 0;

         ok = cyc.randomize() with {kind == wb_cycle::READ;
                                    addr == 32'h0000_0004;  // INT_SOURCE
                                    sel  == 4'hF;};
         if (!ok) begin
            `vmm_fatal(this.log, "Unable to create READ cycle to INT_SOURCE");
         end
         this.host.exec_chan.put(cyc);
         if (cyc.status !== wb_cycle::ACK) begin
            `vmm_error(this.log, "Unable to read INT_SOURCE");
         end

         // Do an immediate write-back to clear the interrupts
         // so we won't miss one
         cyc.kind = wb_cycle::WRITE;
         this.host.exec_chan.put(cyc);
         if (cyc.status !== wb_cycle::ACK) begin
            `vmm_error(this.log, "Unable to write to INT_SOURCE");
         end

         // Analyze the cause(s) for the interrupt
         isr = cyc.data;
         if (isr[1]) begin // TXE
            `vmm_error(this.log, "An error occured during the transmission of a frame");
         end
         
         if (isr[1] || isr[0]) begin // TXB
            integer n = 0;

            `vmm_trace(this.log, "A frame has been transmitted...");

            isr[1:0] = 2'b00;

            if (this.busy_txbd.size() == 0) begin
               `vmm_error(this.log, "Internal error: No busy TXBD");
            end
            
            // A frame has been transmitted, check the transmit buffers...
            while (this.busy_txbd.size() > 0) begin
               bit [31:0] bd_addr = this.busy_txbd[0];

               // Check if that TxBD has been transmitted
               ok = cyc.randomize() with {kind == wb_cycle::READ;
                                          addr == bd_addr;
                                          sel  == 4'hF;};
               if (!ok) begin
                  `vmm_fatal(this.log, "Unable to create READ cycle to TxBD");
               end
               this.host.exec_chan.put(cyc);
               if (cyc.status !== wb_cycle::ACK) begin
                  `vmm_error(this.log, "Unable to read TxBD");
               end

               // Has this frame been transmitted?
               if (cyc.data[15]) begin
                  // No. This implies the subsequent frames have not
                  // been transmitted either
                  if (n == 0) `vmm_error(this.log, "No transmitted TxBD were found");
                  break;
               end

               `vmm_trace(this.log, $psprintf("Frame from TxBD @ 'h%h was transmitted",
                                              bd_addr));

               // What errors happened when the frame was transmitted?
               if (cyc.data[8]
                   || cyc.data[3]
                   || cyc.data[2]) begin
                  string descr = "";
                  string separator = " ";
                  if (cyc.data[8]) begin
                     descr = " Under-run";
                     separator = "/";
                  end
                  if (cyc.data[3]) begin
                     descr = {descr, separator, "Retry Limit"};
                     separator = "/";
                  end
                  if (cyc.data[2]) descr = {descr, separator, "Late Coll"};

                  `vmm_warning(this.log, {"Frame was transmitted with following errors:", descr});
               end
                   
               // What non-errors happened?
               `vmm_trace(this.log, $psprintf("Frame was transmitted with %0d attempts%s%s",
                                              cyc.data[7:4],
                                              (cyc.data[1]) ? ", deferred" : "",
                                              (cyc.data[0]) ? ", carrier lost" : ""));
               

               // Indicate this TxBD is now available
               n++;
               this.avail_txbd.push_back(bd_addr);
               void'(this.busy_txbd.pop_front());
               // Check if the wrap indicator comes next
               if (this.busy_txbd.size() > 0 &&
                   this.busy_txbd[0] == 32'hFFFF_FFFF) begin
                  this.avail_txbd.push_back(32'hFFFF_FFFF);
                  void'(this.busy_txbd.pop_front());
               end
               -> this.avail_txbd_e;
            end
         end // TXB

         if (isr[3]) begin // RXE
`ifndef OC_ETHERNET_BUG
            `vmm_error(this.log, "An error occured during the reception of a frame");
`endif
         end
         
         if (isr[3] || isr[2]) begin // RXB
            integer n = 0;

            `vmm_trace(this.log, "A frame has been received...");

            isr[3:2] = 2'b00;
            
            // A frame has been received, check the receive buffers...
            forever begin
               bit [31:0] bd_addr = this.next_rxbd;
               bit [31:0] rx_pnt;
               bit [15:0] len;
               logic [7:0] bytes[];

               // Check if that RxBD contains a received frame
               ok = cyc.randomize() with {kind == wb_cycle::READ;
                                          addr == bd_addr;
                                          sel  == 4'hF;};
               if (!ok) begin
                  `vmm_fatal(this.log, "Unable to create READ cycle to RxBD");
               end
               this.host.exec_chan.put(cyc);
               if (cyc.status !== wb_cycle::ACK) begin
                  `vmm_error(this.log, "Unable to read RxBD");
               end

               // Is there a frame in there?
               if (cyc.data[15]) begin
                  // No. This implies the subsequent buffers are empty as well
                  if (n == 0) `vmm_error(this.log, "No received RxBD were found");
                  break;
               end
               n++;
               len = cyc.data[31:16];
               
               `vmm_trace(this.log, $psprintf("Frame from RxBD @ 'h%h was received",
                                              bd_addr));

               // What errors happened when the frame was transmitted?
               if (cyc.data[6:0]) begin
                  string descr = "";
                  string separator = " ";
                  if (cyc.data[0]) begin
                     descr = " Late Collision";
                     separator = "/";
                  end
                  if (cyc.data[1]) begin
                     descr = {descr, separator, "Bad CRC"};
                     separator = "/";
                  end
                  if (cyc.data[2]) begin
                     descr = {descr, separator, "Too Short"};
                     separator = "/";
                  end
                  if (cyc.data[3]) begin
                     descr = {descr, separator, "Too Long"};
                     separator = "/";
                  end
                  if (cyc.data[4]) begin
                     descr = {descr, separator, "Dribble"};
                     separator = "/";
                  end
                  if (cyc.data[5]) begin
                     descr = {descr, separator, "Bad Symbol"};
`ifdef OC_ETHERNET_BUG
                     ignore_fr = 1;
`endif
                     separator = "/";
                  end
                  if (cyc.data[6]) begin
                     descr = {descr, separator, "OverRun"};
                     separator = "/";
                  end

                  `vmm_warning(this.log, {"Frame was received with following errors:", descr});
               end
                   
               // Indicate this RxBD is now free
               val = cyc.data;
               val[15] = 1;
               ok = cyc.randomize() with {kind == wb_cycle::WRITE;
                                          addr == bd_addr;
                                          data == val;
                                          sel  == 4'hF;};
               if (!ok) begin
                  `vmm_fatal(this.log, "Unable to create WRITE cycle to RxBD");
               end
               this.host.exec_chan.put(cyc);
               if (cyc.status !== wb_cycle::ACK) begin
                  `vmm_error(this.log, "Unable to write RxBD");
               end

               // Get the frame from the buffer
               rx_pnt = this.cfg.txrx_pnt[bd_addr];
            
               // We'll be recovering full DWORDs
               bytes = new [len + (4 - len % 4)];
               for (int i = 0; i < len; i += 4) begin
                  {bytes[i], bytes[i+1], bytes[i+2], bytes[i+3]} = this.ram.read(rx_pnt + i);
               end
               begin
                  eth_frame fr = new;
                  void'(fr.byte_unpack(bytes, 0, len-4)); // Do not unpack FCS
                  if (val[1]) fr.fcs = 32'hFFFF_FFFF;

                  `vmm_trace(this.log, $psprintf("Retreived RX Frame from 'h%h:\n%s",
                                                 rx_pnt, fr.psdisplay("   ")));

                  if (!ignore_fr) begin
                     this.sb.received_by_mac_side(fr);
                  end
               end

               // Move on to the next RxBD
               next_rxbd += 8;
               if (val[13]) next_rxbd = 32'h0000_0400 + this.cfg.rx_bd_offset * 8;
            end
         end // RXB

         if (isr[4]) begin // BUSY
`ifndef OC_ETHERNET_BUG
            `vmm_error(this.log, "Out of Rx buffers!");
`endif
            isr[4] = 0;
         end

         if (isr) begin
            `vmm_error(this.log, $psprintf("Unserviced interrupts: %h", isr));
         end
      end
   endtask: int_serv
endclass


class wb_cycle_resp_no_wss extends wb_cycle_resp;
   function new(wb_cycle     req,
                wb_slave_cfg cfg);
      super.new(req, cfg);
   endfunction

   constraint no_wss {
      n_wss == 0;
   }

   function vmm_data copy(vmm_data to);
      wb_cycle_resp_no_wss tr;

      if (to == null) tr = new(null, null);
      else if (!$cast(tr, to)) begin
         `vmm_fatal(this.log, "Unable to copy to non-wb_cycle_resp_no_wss instance");
         return null;
      end

      copy = super.copy(tr);
   endfunction: copy

endclass


// Example 5-37
class dut_eth_frame extends eth_frame;
   test_cfg cfg;

   constraint match_dut_address {
      if (!cfg.mac.promiscuous) dst == cfg.dut_addr;
   }

   constraint valid_src_address {
      src == cfg.mac.addr;
   }

   function new(test_cfg cfg);
      this.cfg = cfg;
   endfunction: new
endclass: dut_eth_frame


// Example 4-13
// Example 4-18
class tb_env extends vmm_env;
   test_cfg cfg;

   // Example 4-20
   eth_frame_atomic_gen host_src;
   eth_frame_atomic_gen phy_src;

   eth_mac       mac;
   mii_phy_layer phy;
   mii_monitor   mon;

   wb_master host;
   wb_slave  slv;
   wb_ram    ram;

   sw_emulator swem;

   // Example 5-47
   scoreboard sb;

   // Example 4-18
   // Example 4-19
   function new();
      super.new();
      this.cfg = new;
      $timeformat(-9, 0, "ns", 1);
   endfunction: new

   virtual function void gen_cfg();
      super.gen_cfg();

      this.cfg.wb.max_addr = 32'hFFFF_FFFF;
      this.cfg.wb.min_addr = 32'h0000_0000;
      this.cfg.wb.max_addr.rand_mode(0);
      this.cfg.wb.min_addr.rand_mode(0);

      if (!this.cfg.randomize()) begin
         `vmm_fatal(log, "Failed to randomize test configuration");
      end
   endfunction: gen_cfg


   // Example 4-19
   virtual function void build();
      // Example 4-63
      annotated_eth_frame ann_fr = new;

      super.build();

      `vmm_note(this.log, this.cfg.psdisplay());

      fork
         tb_top.mii.mii_FullDuplex    <= this.cfg.mii.full_duplex;
      join_none

      // Example 5-47
      this.sb = new(this.cfg);

      this.phy_src = new("Phy Side", 0);
      this.phy_src.stop_after_n_insts = this.cfg.run_for_n_rx_frames;

      this.mac = new("PHY Side", 0, this.cfg.mac,
                     this.phy_src.out_chan);

      // Example 4-63
      ann_fr = new;
      ann_fr.direction = "MAC->PHY";
      // Example 4-13
      this.phy = new("PHY Side", 0, this.cfg.mii,
                     tb_top.mii.phy_layer,
                     this.mac.pls_tx_chan,
                     this.mac.pls_rx_chan,
                     this.mac.indications,
                     ann_fr);
      this.mon = new("Passive", 0, this.cfg.mii, tb_top.mii.passive);
      this.mon.to_mac_chan.sink();
      this.mon.to_phy_chan.sink();

      this.host = new("Host", 1, this.cfg.wb, tb_top.wb_sl);
      begin
         wb_cycle_resp_no_wss no_wss_resp = new(null, this.cfg.wb);
         this.ram  = new("RAM",  1, null, null, no_wss_resp);
      end
      this.slv  = new("Slave",  1, this.cfg.wb, tb_top.wb_ma,
                      this.ram.req_chan, this.ram.resp_chan);
      this.swem = new("SW", 1, this.cfg, this.sb, this.host, this.ram);
      this.host_src = new("Host Side", 1, this.swem.tx_chan);
      this.host_src.stop_after_n_insts = this.cfg.run_for_n_tx_frames;

      // Host BFM needed right away to configure DUT
      this.host.start_xactor();

      // Integrate scoreboard
      // Example 4-21
      // Example 5-53
      begin
         sb_mac_cbs cb = new(this.sb);
         this.mac.append_callback(cb);
      end
      // Example 5-54
      fork
         forever begin
            eth_frame fr;
            this.mac.rx_chan.get(fr);
            this.sb.received_by_phy_side(fr);
         end
      join_none

//      this.phy.log.set_verbosity(vmm_log::DEBUG_SEV ,);
//      this.mac.log.set_verbosity(vmm_log::DEBUG_SEV ,);
//      this.log.set_verbosity(vmm_log::TRACE_SEV ,);
//      this.swem.log.set_verbosity(vmm_log::TRACE_SEV ,);
//      this.host.log.set_verbosity(vmm_log::TRACE_SEV ,);
//      this.slv.log.set_verbosity(vmm_log::DEBUG_SEV ,);
//      this.ram.log.set_verbosity(vmm_log::DEBUG_SEV ,);
      this.log.disable_types(vmm_log::INTERNAL_TYP , "/./", "/./");
   endfunction: build


   virtual task reset_dut();
      super.reset_dut();

      tb_top.tx_rx_offset <= this.cfg.tx_rx_clk_offset;
      tb_top.mii_100Mb    <= ~this.cfg.mii.is_10Mb;

      tb_top_env.reset();
   endtask: reset_dut

      
   virtual task cfg_dut();
      bit [31:0] val;
      wb_cycle   cyc = new(this.cfg.wb);
      bit        ok;

      super.cfg_dut();

      // Interpret the configuration descriptor and program the
      // DUT accordingly

      // MODER
      val = 17'b1_1110_0000_0100_0000;
      val[14] = this.cfg.huge_enable;
      val[10] = this.cfg.mac.full_duplex;
      val[5] = this.cfg.mac.promiscuous;
      ok = cyc.randomize() with {kind == wb_cycle::WRITE;
                                 addr == 32'h0000_0000;
                                 data == val;
                                 sel  == 4'hF;};
      if (!ok) begin
         `vmm_fatal(this.log, "Unable to create WRITE cycle to MODER");
      end
      this.host.exec_chan.put(cyc);
      if (cyc.status !== wb_cycle::ACK) begin
         `vmm_error(this.log, "Unable to write to MODER");
      end

      // INT_MASK
      val = 32'h0000_000F;
      ok = cyc.randomize() with {kind == wb_cycle::WRITE;
                                 addr == 32'h0000_0008;
                                 data == val;
                                 sel  == 4'hF;};
      if (!ok) begin
         `vmm_fatal(this.log, "Unable to create WRITE cycle to INT_MASK");
      end
      this.host.exec_chan.put(cyc);
      if (cyc.status !== wb_cycle::ACK) begin
         `vmm_error(this.log, "Unable to write to INT_MASK");
      end

      // IPGT
      val = (this.cfg.mac.full_duplex) ? 16'h15 : 16'h12;
      ok = cyc.randomize() with {kind == wb_cycle::WRITE;
                                 addr == 32'h0000_000C;
                                 data == val;
                                 sel  == 4'hF;};
      if (!ok) begin
         `vmm_fatal(this.log, "Unable to create WRITE cycle to IPGT");
      end
      this.host.exec_chan.put(cyc);
      if (cyc.status !== wb_cycle::ACK) begin
         `vmm_error(this.log, "Unable to write to INT_IPGT");
      end

      // PACKETLEN
      val = {16'h000F, this.cfg.max_frame_len};
      ok = cyc.randomize() with {kind == wb_cycle::WRITE;
                                 addr == 32'h0000_0018;
                                 data == val;
                                 sel  == 4'hF;};
      if (!ok) begin
         `vmm_fatal(this.log, "Unable to create WRITE cycle to PACKETLEN");
      end
      this.host.exec_chan.put(cyc);
      if (cyc.status !== wb_cycle::ACK) begin
         `vmm_error(this.log, "Unable to write to PACKETLEN");
      end

      // TX_BD_NUM
      val = this.cfg.rx_bd_offset;
      ok = cyc.randomize() with {kind == wb_cycle::WRITE;
                                 addr == 32'h0000_0020;
                                 data == val;
                                 sel  == 4'hF;};
      if (!ok) begin
         `vmm_fatal(this.log, "Unable to create WRITE cycle to TX_BD_NUM");
      end
      this.host.exec_chan.put(cyc);
      if (cyc.status !== wb_cycle::ACK) begin
         `vmm_error(this.log, "Unable to write to TX_BD_NUM");
      end

      // CTRLMODER
      val = 32'b0111;
      ok = cyc.randomize() with {kind == wb_cycle::WRITE;
                                 addr == 32'h0000_0024;
                                 data == val;
                                 sel  == 4'hF;};
      if (!ok) begin
         `vmm_fatal(this.log, "Unable to create WRITE cycle to CTRLMODER");
      end
      this.host.exec_chan.put(cyc);
      if (cyc.status !== wb_cycle::ACK) begin
         `vmm_error(this.log, "Unable to write to CTRLMODER");
      end

      // MAC_ADDR0
      val = this.cfg.dut_addr[31:0];
      ok = cyc.randomize() with {kind == wb_cycle::WRITE;
                                 addr == 32'h0000_0040;
                                 data == val;
                                 sel  == 4'hF;};
      if (!ok) begin
         `vmm_fatal(this.log, "Unable to create WRITE cycle to MAC_ADDR0");
      end
      this.host.exec_chan.put(cyc);
      if (cyc.status !== wb_cycle::ACK) begin
         `vmm_error(this.log, "Unable to write to MAC_ADDR0");
      end

      // MAC_ADDR1
      val = {16'h0000,
             this.cfg.dut_addr[47:32]};
      ok = cyc.randomize() with {kind == wb_cycle::WRITE;
                                 addr == 32'h0000_0044;
                                 data == val;
                                 sel  == 4'hF;};
      if (!ok) begin
         `vmm_fatal(this.log, "Unable to create WRITE cycle to MAC_ADDR1");
      end
      this.host.exec_chan.put(cyc);
      if (cyc.status !== wb_cycle::ACK) begin
         `vmm_error(this.log, "Unable to write to MAC_ADDR1");
      end

      // Example 5-22
      // Example 5-36
      // Make sure the frame generators generate frames with the
      // correct DA & SA
      this.host_src.randomized_obj.dst = this.cfg.mac.addr;
      this.host_src.randomized_obj.dst.rand_mode(0);
      this.host_src.randomized_obj.src = this.cfg.dut_addr;
      this.host_src.randomized_obj.src.rand_mode(0);

      // Example 5-37
      begin
         dut_eth_frame fr = new(this.cfg);
         this.phy_src.randomized_obj = fr;
      end

      // Initialize the required number of buffer descriptors
      begin
         bit [31:0] bd_addr;
         integer i;

         // Tx BD
         bd_addr = 32'h0000_0400;
         `vmm_trace(this.log, $psprintf("Configuring %0d TxBD starting at 32'h%h",
                                        this.cfg.n_tx_bd, bd_addr));
         for (i = this.cfg.n_tx_bd; i > 0; i--) begin
            val = 32'h0000_4000;
            if (i == 1) val[13] = 1'b1;
            ok = cyc.randomize() with {kind == wb_cycle::WRITE;
                                       addr == bd_addr;
                                       data == val;
                                       sel  == 4'hF;};
            if (!ok) begin
               `vmm_fatal(this.log, "Unable to create WRITE cycle to TxBD");
            end
            this.host.exec_chan.put(cyc);
            if (cyc.status !== wb_cycle::ACK) begin
               `vmm_error(this.log, "Unable to write to TxBD");
            end
            val = this.cfg.txrx_bfr_base + i * ((this.cfg.huge_enable) ? 65536 : this.cfg.max_frame_len);
            this.cfg.txrx_pnt[bd_addr] = val;
            bd_addr += 4; // Buffer pointer
            ok = cyc.randomize() with {kind == wb_cycle::WRITE;
                                       addr == bd_addr;
                                       data == val;
                                       sel  == 4'hF;};
//$write("***bd_addr=%h, addr=%h (%b) val=%h, data=%h (%b)\n", bd_addr, cyc.addr, (cyc.addr == bd_addr),
//       val, cyc.data, cyc.data == val);
            if (!ok) begin
               `vmm_fatal(this.log, "Unable to create WRITE cycle to TxBD.TxPNT");
            end
            this.host.exec_chan.put(cyc);
            if (cyc.status !== wb_cycle::ACK) begin
               // Example 4-26
               `vmm_error(this.log, "Unable to write to TxBD.TxPNT");
            end
            bd_addr += 4;

            `vmm_debug(this.log, $psprintf("TxBD #%0d points to 'h%h", i, val));
         end

         // Rx BD
         bd_addr = 32'h0000_0400 + this.cfg.rx_bd_offset * 8;
         `vmm_trace(this.log, $psprintf("Configuring %0d RxBD starting at 32'h%h",
                                        this.cfg.n_rx_bd, bd_addr));
         this.swem.next_rxbd = bd_addr;
         for (i = this.cfg.n_rx_bd; i > 0; i--) begin
            val = 32'h0000_0000;
            val[15] = 1; // Empty
            val[14] = 1; // Generate an interrupt
            if (i == 1) val[13] = 1'b1;  // Last buffer?
            ok = cyc.randomize() with {kind == wb_cycle::WRITE;
                                       addr == bd_addr;
                                       data == val;
                                       sel  == 4'hF;};
            if (!ok) begin
               `vmm_fatal(this.log, "Unable to create WRITE cycle to RxBD");
            end
            this.host.exec_chan.put(cyc);
            if (cyc.status !== wb_cycle::ACK) begin
               `vmm_error(this.log, "Unable to write to RxBD");
            end
            val = this.cfg.txrx_bfr_base + (this.cfg.n_tx_bd + i) *
                   ((this.cfg.huge_enable) ? 65536 : this.cfg.max_frame_len);
            this.cfg.txrx_pnt[bd_addr] = val;
            bd_addr += 4; // Buffer pointer
            ok = cyc.randomize() with {kind == wb_cycle::WRITE;
                                       addr == bd_addr;
                                       data == val;
                                       sel  == 4'hF;};
            if (!ok) begin
               `vmm_fatal(this.log, "Unable to create WRITE cycle to RxBD.RxPNT");
            end
            this.host.exec_chan.put(cyc);
            if (cyc.status !== wb_cycle::ACK) begin
               `vmm_error(this.log, "Unable to write to RxBD.RxPNT");
            end
            bd_addr += 4; // Next BD

            `vmm_debug(this.log, $psprintf("RxBD #%0d points to 'h%h", i, val));
         end
      end

      // Enable Tx & Rx
      `vmm_trace(this.log, "Enabling Tx/Rx paths...");
      ok = cyc.randomize() with {kind == wb_cycle::READ;
                                 addr == 32'h0000_0000;
                                 sel  == 4'hF;};
      if (!ok) begin
         `vmm_fatal(this.log, "Unable to create READ cycle to MODER");
      end
      this.host.exec_chan.put(cyc);
      if (cyc.status !== wb_cycle::ACK) begin
         `vmm_error(this.log, "Unable to read from MODER");
      end
      val = cyc.data;
      val[1:0] = 2'b11;
      ok = cyc.randomize() with {kind == wb_cycle::WRITE;
                                 addr == 32'h0000_0000;
                                 data == val;
                                 sel  == 4'hF;};
      if (!ok) begin
         `vmm_fatal(this.log, "Unable to create WRITE cycle to MODER");
      end
      this.host.exec_chan.put(cyc);
      if (cyc.status !== wb_cycle::ACK) begin
         `vmm_error(this.log, "Unable to write to MODER");
      end
   endtask: cfg_dut

   // Example 4-22
   virtual task start();
      super.start();
      if (this.cfg.run_for_n_tx_frames > 0) this.host_src.start_xactor();
      if (this.cfg.run_for_n_rx_frames > 0) this.phy_src.start_xactor();
      this.mac.start_xactor();
      // Example 4-13
      this.phy.start_xactor();
      this.slv.start_xactor();
      this.ram.start_xactor();
      this.swem.start_xactor();
   endtask: start

   // Example 4-17
   virtual task wait_for_end();
      super.wait_for_end();

      // Example 4-24
      fork
         @ (this.end_test) disable wait_for_end;
      join_none

      // Example 4-23
      wait (this.cfg.run_for_n_tx_frames == 0 &&
            this.cfg.run_for_n_rx_frames == 0);
      disable fork;
   endtask: wait_for_end

   virtual task stop();
      super.stop();

      this.host_src.stop_xactor();
      this.phy_src.stop_xactor();
      
      // Let the system drain of all in-flight frames
      // ToDo...
   endtask: stop

   virtual task cleanup();
      super.cleanup();
   endtask: cleanup
endclass
