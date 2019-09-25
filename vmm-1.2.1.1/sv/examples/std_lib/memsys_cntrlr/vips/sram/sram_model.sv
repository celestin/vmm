//
// -------------------------------------------------------------
//    Copyright 2004-2009 Synopsys, Inc.
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

typedef class sram_model;

class sram_model_callbacks extends vmm_xactor_callbacks;
    /*virtual function void pre_trans(sram_model drv, sram_trans tr, ref bit drop);
    endfunction
    virtual function void post_trans(sram_model drv, sram_trans tr);
    endfunction */
virtual task pre_trans(sram_model drv, sram_trans tr, ref bit drop);
    endtask
    virtual task post_trans(sram_model drv, sram_trans tr);
    endtask
endclass

class sram_model extends vmm_xactor;
`vmm_typename(sram_model)
  virtual sram_if.memprt  iport;
  sramport                sram_port_obj;
  vmm_tlm_analysis_port #(sram_model, sram_trans) analysis_port;
  reg  [7:0]              memQ[*];
  string                  resp_kind;
  bit [31:0]              start_addr;
  bit [31:0]              end_addr;
  local bit               is_done;


  extern function new(string inst, vmm_unit parent=null);
  extern virtual function void build_ph();
  extern virtual function void configure_ph();
  extern virtual function void connect_ph();
  extern virtual function void start_of_sim_ph();
  extern virtual task shutdown_ph();
  extern virtual task run_ph();
endclass

function sram_model::new(string inst, vmm_unit parent);
  super.new(get_typename(), inst, 0, parent);
endfunction

task sram_model::run_ph();
   iport.ramData <= 8'hzz;
   fork begin
      fork 
        while (1) begin : w0
           bit [31:0] addr;
           sram_trans   tr;
           wait (~iport.ce_N && iport.rdWr_N);
           addr = iport.ramAddr;
           tr = new();
           tr.address = addr;
           tr.kind = sram_trans::READ;
           if (addr >= start_addr && addr <= end_addr) begin
              if (memQ.exists(addr)) begin
                 iport.ramData = #5 memQ[addr];
                 tr.data = memQ[addr];
              end
              else begin
                 reg [7:0] data;
                 case(resp_kind)
                    "RESP_00"  : data = 0;
                    "RESP_FF"  : data = 8'hff;
                    "RESP_XX"  : data = 8'hx;
                    "RESP_RAND": data = $random();
                 endcase
                 memQ[addr] = data;
                 tr.data = data;
                 iport.ramData = #5 data;
              end
               if (is_done) break;
              `vmm_callback(sram_model_callbacks, post_trans(this, tr));
              analysis_port.write(tr);
           end
           @(iport.cb);
           iport.ramData = #5 8'hzz;
        end : w0
        while (1) begin : w1
           bit [31:0] addr;
           sram_trans tr;
           wait (~iport.cb.ce_N && ~iport.cb.rdWr_N);
           tr = new();
           addr = iport.ramAddr;
           tr.kind = sram_trans::WRITE;
           tr.address = addr;
           memQ[addr] = iport.ramData;
           tr.data = memQ[addr];
           `vmm_callback(sram_model_callbacks, post_trans(this, tr));
           analysis_port.write(tr);
           @(iport.cb);
        end : w1
        wait (is_done); 
      join_any
      disable fork;
      is_done = 0;
   end join_none
endtask

function void sram_model::build_ph();
  analysis_port = new(this, {get_object_name(), "_analysis_port"});
endfunction

function void sram_model::configure_ph();
begin
    `vmm_unit_config_string(resp_kind, "RESP_RAND", {"Configures default response value for SRAM model ", get_instance()}, 0, DO_ALL)
    `vmm_unit_config_int(start_addr, 0, {"Configures Start address for SRAM model ", get_instance()}, 0, DO_ALL)
    `vmm_unit_config_int(end_addr, 'hffff_ffff, {"Configures End address for SRAM model ", get_instance()}, 0, DO_ALL)
end
endfunction

function void sram_model::connect_ph();
   bit is_set;
   if ($cast(sram_port_obj, vmm_opts::get_object_obj(is_set,this,"sram_port"))) begin
      if (sram_port_obj != null)
       this.iport = sram_port_obj.iport;
      else
       `vmm_fatal(log, "Virtual port wrapper not initialized");
   end
endfunction

function void sram_model::start_of_sim_ph();
   void'(this.randomize());
   if (iport == null)
       `vmm_fatal(log, "Virtual port not connected to the actual interface instance");
endfunction

task sram_model::shutdown_ph();
   is_done = 1;
   this.stop_xactor();
endtask

