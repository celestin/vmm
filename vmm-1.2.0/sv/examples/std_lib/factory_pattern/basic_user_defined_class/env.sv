
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


class ahb_gen extends vmm_unit;
`vmm_typename(ahb_gen)
   ahb_trans tr;

   function new(string name);
     super.new(get_typename(), name);
   endfunction

   virtual function void build_ph();
     tr = ahb_trans::create_instance(this, "Ahb_Tr0", `__FILE__, `__LINE__); 
    // `vmm_note(log, $psprintf("Ahb transaction type is %s", tr.get_typename()));
	 if(!((tr.get_typename() =="class P.ahb_trans") || (tr.get_typename() == "class P.my_ahb_trans")))
        `vmm_error(log,"ERROR");
   endfunction

endclass

initial begin
  ahb_gen gen0 = new("gen0");
  ahb_gen gen1 = new("gen1");
  ahb_trans tr;
  my_ahb_trans mtr;
  vmm_log log = new("prgm", "prgm");

  gen0.build_ph();
//  $display("Gen0.Addr = %x", gen0.tr.addr);
	if(gen0.tr.addr !==00)
        `vmm_error(log,"Error1");


  tr = new("gen0_trans", null, 5);
  ahb_trans::override_with_copy("@%*", tr, log, `__FILE__, `__LINE__);
  gen0.build_ph();
//  $display("Gen0.Addr = %x", gen0.tr.addr);
	if(gen0.tr.addr !==05)
        `vmm_error(log,"Error1");


  ahb_trans::override_with_new("@%*", my_ahb_trans::this_type, log, `__FILE__, `__LINE__);
  gen0.build_ph();
  gen1.build_ph();
//  $display("Gen0.Addr = %x", gen0.tr.addr);
 // $display("Gen1.Addr = %x", gen1.tr.addr);
if(gen0.tr.addr !==00)
        `vmm_error(log,"Error1");
if(gen1.tr.addr !==00)
        `vmm_error(log,"Error1");


  mtr = new("gen1_trans", null, 50, 500);
  my_ahb_trans::override_with_copy("@%*", mtr, log, `__FILE__, `__LINE__);
  gen1.build_ph();
//  $display("Gen0.Addr = %x", gen0.tr.addr);
 // $display("Gen1.Addr = %x", gen1.tr.addr);
	if(gen0.tr.addr !==00)
        `vmm_error(log,"Error1");
	if(gen1.tr.addr !==00)
        `vmm_error(log,"Error1");


 log.report();
end

endprogram



