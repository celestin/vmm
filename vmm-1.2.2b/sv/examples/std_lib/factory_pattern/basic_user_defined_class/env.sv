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

`define VMM_12
program P;
`include "vmm.sv"

class ahb_trans;
  `vmm_typename(ahb_trans)
  string name;
  vmm_object parent;
  rand bit [7:0] addr;
  static vmm_log log;

  function new(string name = "", vmm_object parent = null, bit[7:0] addr=0);
     log = new(this.get_typename(), "object");
     this.name = name;
     this.parent = parent;
     this.addr = addr;
  endfunction
  
  virtual function ahb_trans allocate();
    allocate = new;
  endfunction

  virtual function ahb_trans copy();
    copy = new(this.name, this.parent, this.addr);
  endfunction

  `vmm_class_factory(ahb_trans)
endclass

class my_ahb_trans extends ahb_trans;
  `vmm_typename(my_ahb_trans)
  rand bit [7:0] data;


  function new(string name = "", vmm_object parent = null, bit[7:0] addr=0, bit[7:0] data=0);
    super.new(name, parent, addr);
    this.data = data;
  endfunction
  
  virtual function my_ahb_trans copy();
     my_ahb_trans tr = new(this.name, this.parent, this.addr, this.data);
     return tr;
  endfunction

  virtual function my_ahb_trans allocate();
    allocate = new;
  endfunction

  `vmm_class_factory(my_ahb_trans)

endclass


class ahb_gen extends vmm_group;
`vmm_typename(ahb_gen)
   ahb_trans tr;

   function new(string name, string inst, vmm_group parent=null);
    // super.new(name , inst, parent);
     super.new(get_typename(), inst, parent);
   endfunction

   virtual task config_dut_ph();

     tr = ahb_trans::create_instance(this, "Ahb_Tr0", `__FILE__, `__LINE__); 
    // `vmm_note(log, $psprintf("Ahb transaction type is %s", tr.get_typename()));
	 if(!((tr.get_typename() =="class P.ahb_trans") || (tr.get_typename() == "class P.my_ahb_trans")))
        `vmm_error(log,"ERROR");
   endtask

endclass


initial begin
  vmm_timeline       topTimeline = new("mytime", "mytime");
  ahb_gen             gen0 = new("gen0","gen0_group",topTimeline);
  ahb_gen			  gen1 = new("gen1","gen1_group",topTimeline);

  ahb_trans tr;
  my_ahb_trans mtr;
  
  vmm_log log = new("prgm", "prgm");
  
  
  topTimeline.run_phase("config_dut");

	if(gen0.tr.addr !==00)
        `vmm_error(log,"Error1");

  topTimeline.reset_to_phase("configure_test");

  tr = new("gen0_trans", null, 5);
  topTimeline.run_phase("start_of_sim");
  ahb_trans::override_with_copy("@%*", tr, log, `__FILE__, `__LINE__);
  topTimeline.run_phase(); 

  $display("After override_with_copy Gen0.Addr = %x", gen0.tr.addr);
	if(gen0.tr.addr !==05)
        `vmm_error(log,"Error2");

  topTimeline.reset_to_phase("start_of_sim");
  ahb_trans::override_with_new("@%*", my_ahb_trans::this_type, log, `__FILE__, `__LINE__);
  
  $display("After override_with_new Gen0.Addr  = %x", gen0.tr.addr);
  $display("After override_with_new Gen1.Addr  = %x", gen1.tr.addr);
	if(gen0.tr.addr !==05)
        `vmm_error(log,"Error3");
	if(gen1.tr.addr !==05)
        `vmm_error(log,"Error4");


  mtr = new("gen1_trans", null, 50, 500);
  ahb_trans::override_with_copy("@%*", mtr, log, `__FILE__, `__LINE__);
  topTimeline.run_phase(); 
  $display("After override_with_copy Gen0.Addr = %x", gen0.tr.addr);
  $display("After override_with_copy Gen1.Addr = %x", gen1.tr.addr);
	if(gen0.tr.addr !==50)
        `vmm_error(log,"Error5");
	if(gen1.tr.addr !==50)
        `vmm_error(log,"Error6");

 log.report();
end

endprogram



