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

typedef class cpu_driver;

class cpu_driver_callbacks extends vmm_xactor_callbacks;
    virtual task pre_trans  (cpu_driver driver,
                               cpu_trans tr,
                               ref bit drop);
    endtask


   virtual task post_trans  (cpu_driver driver,
                               cpu_trans tr
                               );
   endtask
endclass

class cpu_driver extends vmm_xactor;
  `vmm_typename(cpu_driver)

  virtual cpu_if.drvprt  iport;
  cpu_trans_channel in_chan;
  cpuport cpu_port_obj;
  vmm_tlm_analysis_port#(cpu_driver, cpu_trans) pre_analysis_port;
  vmm_tlm_analysis_port#(cpu_driver, cpu_trans) analysis_port;
  local bit is_done;

  extern function new(string inst="", vmm_unit parent=null);
  extern virtual task run_ph();
  extern task write_op(cpu_trans tr);
  extern task read_op(cpu_trans tr);
  extern virtual function void build_ph();
  extern virtual function void connect_ph();
  extern virtual function void start_of_sim_ph();
  extern task shutdown_ph();
  extern virtual function cpu_driver allocate();
  extern virtual function cpu_driver copy();

  `vmm_class_factory(cpu_driver)
endclass

function cpu_driver::new(string inst, vmm_unit parent);
  super.new(get_typename(), inst, 0, parent);
endfunction

function void cpu_driver::build_ph();
  analysis_port = new(this, {get_object_name(), "_analysis_port"});
  pre_analysis_port = new(this, {get_object_name(), "_pre_analysis_port"});
endfunction

task cpu_driver::run_ph();
   bit drop;
   cpu_trans   tr;
   is_done = 0;
   fork 
     while (1) begin : w0
       this.in_chan.peek(tr);
       if (is_done) break;
       `vmm_trace (this.log, $psprintf ("Driver received a transaction: %s", tr.psdisplay()));
       `vmm_callback(cpu_driver_callbacks, pre_trans(this, tr, drop));
       this.pre_analysis_port.write(tr);
       if (tr.kind == cpu_trans::WRITE) begin
         write_op(tr);
       end
       if (tr.kind == cpu_trans::READ) begin
         read_op(tr);
       end
       `vmm_callback(cpu_driver_callbacks, post_trans(this, tr));
       this.analysis_port.write(tr);
       this.in_chan.get(tr);
       wait_if_stopped();
       if (is_done) break;
     end : w0
   join_none
endtask

task cpu_driver::write_op(cpu_trans tr);
    repeat (tr.trans_delay) @(iport.cb);
    iport.cb.busAddr <= tr.address;
    iport.cb.busData <= tr.data; 
    iport.cb.busRdWr_N <= 1'b0; 
    iport.cb.adxStrb <= 1'b1; 
    @(iport.cb);
    iport.cb.busRdWr_N <= 1'b1; 
    iport.cb.busData <= 8'bzzzzzzzz; 
    iport.cb.adxStrb <= 1'b0;    
    repeat (4) @(iport.cb);
endtask

task cpu_driver::read_op(cpu_trans tr);
    repeat (tr.trans_delay) @(iport.cb);
    iport.cb.busAddr <= tr.address;
    iport.cb.busRdWr_N <= 1'b1;
    iport.cb.adxStrb <= 1'b1; 
    @(iport.cb);
    iport.cb.adxStrb <= 1'b0;
    repeat (3) @(iport.cb);
    tr.data = iport.cb.busData;
endtask

function void cpu_driver::connect_ph();
   bit is_set;
   if ($cast(cpu_port_obj, vmm_opts::get_object_obj(is_set,this,"cpu_port"))) begin
      if (cpu_port_obj != null)
       this.iport = cpu_port_obj.iport;
      else
       `vmm_fatal(log, "Virtual port wrapper not initialized");
   end
endfunction

function void cpu_driver::start_of_sim_ph();
   if (iport == null)
       `vmm_fatal(log, "Virtual port not connected to the actual interface instance");
endfunction

task cpu_driver::shutdown_ph();
   is_done = 1;
endtask

function cpu_driver cpu_driver::copy();
   cpu_driver drv;
   drv = this.allocate();
   return drv;
endfunction

function cpu_driver cpu_driver::allocate();
   vmm_unit prnt;
   cpu_driver drv;
   $cast(prnt, this.get_parent_object());
   drv = new(this.get_object_name(), prnt);
   return drv;
endfunction


