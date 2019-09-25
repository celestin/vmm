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
//vmm_object factory class

`define VMM_12
program P;
`include "vmm.sv"

class ahb_trans extends vmm_object;
  `vmm_typename(ahb_trans)
  rand bit [7:0] addr;
  static vmm_log log = new("ahb_trans", "object");

  virtual function ahb_trans allocate();
    allocate = new(this.get_object_name(), get_parent_object());
  endfunction

  virtual function ahb_trans copy();
     ahb_trans tr = new(this.get_object_name(), get_parent_object());
     tr.addr = this.addr;
     return tr;
  endfunction

  function new(string name = "", vmm_object parent = null);
    super.new(parent, name);
  endfunction
  
  `vmm_class_factory(ahb_trans)

endclass

class my_ahb_trans extends ahb_trans;
  `vmm_typename(my_ahb_trans)

  static vmm_log log = new("my_ahb_trans", "object");

  function new(string name = "", vmm_object parent = null);
    super.new(name, parent);
  endfunction
  
  virtual function my_ahb_trans allocate();
     allocate = new(this.get_object_name(), get_parent_object());
  endfunction

  virtual function my_ahb_trans copy();
     my_ahb_trans tr = new(this.get_object_name(), get_parent_object());
     tr.addr = this.addr;
     return tr;
  endfunction

  `vmm_class_factory(my_ahb_trans)

endclass


class ahb_gen extends vmm_group;
`vmm_typename(ahb_gen)
   ahb_trans tr;

   function new(string name, string instance, vmm_group parent = null);
     super.new(get_typename(), instance, parent);
   endfunction

   virtual task config_dut_ph();
     tr = ahb_trans::create_instance(this, "Ahb_Tr0", `__FILE__, `__LINE__); 
		if(!((tr.get_typename() =="class P.ahb_trans") || (tr.get_typename() == "class P.my_ahb_trans")))
		`vmm_error(log,"ERROR");

   endtask

endclass

initial begin
  vmm_timeline topTimeline = new("topTimeline", "topTimeline");
  ahb_gen gen0 = new("gen0", "gen0", topTimeline);
  ahb_gen gen1 = new("gen1", "gen1", topTimeline);
  ahb_trans tr;
  vmm_log log = new("prgm", "prgm");

  topTimeline.run_phase();
  $display("Default run Gen0.Addr = %x", gen0.tr.addr);
  if(gen0.tr.addr !== 00)
	`vmm_error(log,"Error1");

  topTimeline.reset_to_phase("start_of_sim");
  tr = new("gen0_trans");
  tr.addr = 5;
  ahb_trans::override_with_copy("@%*", tr, log, `__FILE__, `__LINE__);
  topTimeline.run_phase();
  $display("Run after override_with_copy Gen0.Addr = %x", gen0.tr.addr);
  if(gen0.tr.addr !==05)
	`vmm_error(log,"Error2");

  topTimeline.reset_to_phase("start_of_sim");
  ahb_trans::override_with_new("@%*", my_ahb_trans::this_type, log, `__FILE__, `__LINE__);
  topTimeline.run_phase(); 
  $display("Run after override_with_new Gen0.Addr = %x", gen0.tr.addr);
	if(gen0.tr.addr !==00)
	`vmm_error(log,"Error3");
  $display("Run after override_with_new Gen1.Addr = %x", gen1.tr.addr);
	if(gen1.tr.addr !==00)
	`vmm_error(log,"Error4");
log.report();
end

endprogram


