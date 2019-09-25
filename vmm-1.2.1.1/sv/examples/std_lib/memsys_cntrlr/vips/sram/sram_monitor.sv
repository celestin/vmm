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

typedef class sram_monitor;

class sram_monitor_callbacks extends vmm_xactor_callbacks;
    virtual function void post_trans(sram_monitor mon, sram_trans tr);
    endfunction
endclass

class sram_monitor extends vmm_xactor;
`vmm_typename(sram_monitor)
  virtual sram_if.monprt  iport;
  sram_monport            sram_port_obj;
  vmm_tlm_analysis_port #(sram_monitor, sram_trans) analysis_port;
  string                  resp_kind;

  extern function new(string inst, vmm_unit parent=null);
  extern virtual function void build_ph();
  extern virtual function void connect_ph();
  extern virtual function void start_of_sim_ph();
  extern virtual task main();
endclass

function sram_monitor::new(string inst, vmm_unit parent);
  super.new(get_typename(), inst, 0, parent);
endfunction

task sram_monitor::main();
super.main();
   fork 
     while (1) begin : w0
        bit [31:0] addr;
        sram_trans   tr;
        wait (~iport.ce_N && iport.rdWr_N);
        addr = iport.ramAddr;
        tr = new();
        tr.address = addr;
        tr.kind = sram_trans::READ;
        @(iport.cb);
        tr.data = iport.cb.ramData;
        `vmm_callback(sram_monitor_callbacks, post_trans(this, tr));
        analysis_port.write(tr);
     end : w0
     while (1) begin : w1
        bit [31:0] addr;
        sram_trans tr;
        wait (~iport.cb.ce_N && ~iport.cb.rdWr_N);
        tr = new();
        tr.kind = sram_trans::WRITE;
        tr.address = iport.ramAddr;
        tr.data = iport.ramData;
        `vmm_callback(sram_monitor_callbacks, post_trans(this, tr));
        analysis_port.write(tr);
        @(iport.cb);
     end : w1
   join_none
endtask

function void sram_monitor::build_ph();
  analysis_port = new(this, {get_object_name(), "_analysis_port"});
endfunction

function void sram_monitor::connect_ph();
   bit is_set;
   if ($cast(sram_port_obj, vmm_opts::get_object_obj(is_set,this,"sram_monport"))) begin
      if (sram_port_obj != null)
       this.iport = sram_port_obj.iport;
      else
       `vmm_fatal(log, "Virtual port wrapper not initialized");
   end
endfunction

function void sram_monitor::start_of_sim_ph();
   void'(this.randomize());
   if (iport == null)
       `vmm_fatal(log, "Virtual port not connected to the actual interface instance");
endfunction


