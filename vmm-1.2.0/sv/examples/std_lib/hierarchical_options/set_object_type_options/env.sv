`define VMM_12
program test;

`include "vmm.sv"

vmm_log log = new("prgm", "prgm");

class A extends vmm_object;

int foo = 11;
function new( vmm_object parent=null, string name);
	bit is_set;
  super.new(parent, name);
endfunction
endclass


class B extends vmm_object;

A a1;
A a2;

function new(vmm_object parent=null, string name);
  bit is_set;
  super.new(parent, name);
  a1 = new(null, "a1");
  a2 = new(null, "a2");
  a2.foo = 22;
  $cast(a1, vmm_opts::get_object_obj(is_set, this, "OBJ_F1", a2,"SET OBJ", 0));

endfunction

endclass


B b2;
A a3;

initial
begin

a3 = new(null, "a3");
a3.foo = 99;

vmm_opts::set_object("b2:OBJ_F1", a3,null,,);

b2 = new(null, "b2");

$display("\nSet the object type option for the vmm_object \"b2.a1\" ");

$display("\nValue of foo in b2.a1 is %0d (Expected value '99')", b2.a1.foo);
if(b2.a1.foo != 99) `vmm_error(log, `vmm_sformatf(" Value of foo in b2.a1 is %0d instead of 99 \n",b2.a1.foo));

$display("\n");
log.report();
end
endprogram
