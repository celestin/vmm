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


`include "vmm_ral.sv"
`include "wishbone.sv"
`include "ral_oc_ethernet.sv"

class oc_ethernet_env_cfg;
   rand wb_slave_cfg  wb;
      
   constraint oc_ethernet_env_cfg_valid {
      wb.port_size   == wb_cfg::DWORD;
      wb.granularity == wb_cfg::BYTE; 
      wb.cycles      == wb_cfg::CLASSIC;
   }

   function new();
      this.wb  = new;
   endfunction: new
endclass: oc_ethernet_env_cfg


class wb_ral_master extends vmm_rw_xactor;
   wb_cfg    cfg;
   wb_master wb;

   function new(string                inst,
                int unsigned          stream_id,
                wb_cfg                cfg,
                virtual wb_if.master  sigs,
                vmm_rw_access_channel exec_chan = null);
      super.new("Wishbone RAL Master", inst, stream_id, exec_chan);

      this.cfg = cfg;
      this.wb = new(inst, stream_id, cfg, sigs);
   endfunction: new

   
   virtual task execute_single(vmm_rw_access tr);
      wb_cycle cyc;
      bit      ok;
      
      // Translate the generic RW into a wishbone RW
      cyc = new(this.cfg);

      cyc.data_id     = tr.data_id;
      cyc.scenario_id = tr.scenario_id;
      cyc.stream_id   = tr.stream_id;
      
      // Avoid randomization failures
      if (tr.kind == vmm_rw::READ) tr.data = 0;
      ok = cyc.randomize() with {
         cyc.addr == tr.addr << 2; // BYTE granularity in DWORD bus size
         cyc.sel  == 4'hF;         // 32-bit bus
         cyc.lock == 0;
         if (tr.kind == vmm_rw::WRITE) {
            cyc.kind == wb_cycle::WRITE;
            cyc.data == tr.data;
         } else {
            cyc.kind == wb_cycle::READ;
         }
      };
      if (!ok) begin
        `vmm_error(this.log, "Cannot translate RAL R/W cycle into equivalent Wishbone R/W cycle");
         tr.status = vmm_rw::ERROR;
         return;
      end

      this.wb.exec_chan.put(cyc);

      // Send the result back to the RAL
      case (cyc.status)
         wb_cycle::ACK: tr.status = vmm_rw::IS_OK;
         wb_cycle::RTY: tr.status = vmm_rw::RETRY;
         default      : tr.status = vmm_rw::ERROR;
      endcase
      if (tr.kind == vmm_rw::READ) begin
         tr.data = cyc.data;
      end
      else begin
         // Let the assignment to registers physically happen
         // to make sure an immediate back-door readback will
         // read the just-written value
         #2;
      end
   endtask: execute_single

   virtual function void start_xactor();
      super.start_xactor();
      this.wb.start_xactor();
   endfunction: start_xactor

   virtual function void stop_xactor();
      super.stop_xactor();
      this.wb.stop_xactor();
   endfunction: stop_xactor

   virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
      super.reset_xactor(rst_typ);
      this.wb.reset_xactor(rst_typ);
   endfunction: reset_xactor
endclass: wb_ral_master

typedef class oc_ethernet_env;
class gen_cfg_phase_def extends vmm_topdown_function_phase_def #(oc_ethernet_env);
   `vmm_typename(gen_cfg_phase_def)

   function void do_function_phase(oc_ethernet_env obj);
      obj.gen_cfg_ph();
   endfunction:do_function_phase
endclass:gen_cfg_phase_def


class oc_ethernet_env extends vmm_group;
   oc_ethernet_env_cfg cfg;
   wb_ral_master       host;

   vmm_ral_access        ral_rw;
   ral_block_oc_ethernet ral;

   function new(vmm_object parent = null, string name = "");
      super.new("oc_ethernet_env", name, parent);
      this.cfg = new;
      $timeformat(-9, 0, "ns", 1);
      begin
         gen_cfg_phase_def gencfg_ph = new;
         vmm_timeline tl = this.get_timeline();
         tl.insert_phase("gen cfg", "^", gencfg_ph);
      end
   endfunction: new

   virtual function void gen_cfg_ph();
      this.cfg.wb.max_addr = 32'hFFFF_FFFF;
      this.cfg.wb.min_addr = 32'h0000_0000;
      this.cfg.wb.max_addr.rand_mode(0);
      this.cfg.wb.min_addr.rand_mode(0);

      if (!this.cfg.randomize()) begin
         `vmm_fatal(log, "Failed to randomize environment configuration");
      end
   endfunction: gen_cfg_ph


   virtual function void build_ph();
      super.build_ph();

      this.ral_rw = new(this, "ral_rw");
      this.ral = new;
      this.ral_rw.set_model(this.ral);

      this.host = new("Host", 1, this.cfg.wb, tb_top.wb_sl);
      this.ral_rw.add_xactor(this.host);
   endfunction: build_ph


   virtual task reset_ph();
      tb_top.rst <= 1;
      repeat (3) @ (posedge tb_top.wb_clk);
      tb_top.rst <= 0;
   endtask: reset_ph
   
   virtual task run_ph();
      super.run_ph();
      repeat (100) @ (posedge tb_top.wb_clk);
   endtask: run_ph

endclass: oc_ethernet_env
