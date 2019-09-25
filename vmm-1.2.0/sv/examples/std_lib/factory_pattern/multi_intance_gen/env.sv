//mutiple gen instances
program p;
`include "vmm.sv"

class basic;
	int j =1;
endclass

class myclass ;
	`vmm_typename(myclass);
	basic basic_inst ;
	int i =0;

	function new;
	basic_inst = new();
	endfunction

	virtual task mytask;
		i = 1;
	endtask

	virtual function myclass copy();
	myclass tr = new();
		tr.i = this.i;
		tr.basic_inst = new this.basic_inst;
		return tr;
	endfunction

	vmm_log myclslog = new("mycls","mycls");
	virtual function myclass allocate();
		allocate = new();//this.get_object_name(), get_parent_object());
	endfunction

	`vmm_class_factory(myclass);
endclass

class ext extends myclass;
`vmm_typename(ext)
vmm_log ext_log = new("ext","ext");

	function new();
	super.new();
	super.i = 1;
	endfunction

task mytask;
i = 3;
endtask

	virtual function ext copy();
	ext tr = new();
	tr.i = this.i;
	tr.basic_inst = new this.basic_inst;
	return tr;
	endfunction


	virtual function ext allocate();
	allocate = new();//this.get_object_name(), get_parent_object());
	endfunction


`vmm_class_factory(ext);
endclass

class gen extends vmm_unit;
`vmm_typename(gen)
	myclass tr;
	vmm_log log = new("cl","cl");

	virtual function void build_ph();
	tr = myclass::create_instance(this,"mydummyclass", `__FILE__,`__LINE__);
//	`vmm_note(log,$psprintf("new Transction type is **** %d %s", tr.basic_inst.j,tr.get_typename()));
	tr.mytask;
	if(!((tr.i== 3) && (tr.basic_inst.j == 5)))
	`vmm_error(log,"ERROR");
	endfunction

	function new (string name);
	super.new(get_typename(), name);
	endfunction

endclass


class env extends vmm_unit;
`vmm_typename(env)
gen gen0 ;
gen gen1 ;
gen gen2 ;
gen gen3 ;
gen gen4 ;

function new(string name);
super.new(get_typename(), name);
gen0 = new("gen0");
gen1 = new("gen0");
gen2 = new("gen0");
gen3 = new("gen0");
gen4 = new("gen0");
endfunction
vmm_log log1 = new("cl1","cl1");

virtual function void build_ph();
ext ext0 = new();
ext ext1 = new();
ext ext2 = new();
ext ext3 = new();
ext ext4 = new();

ext0.basic_inst.j = 5;
ext1.basic_inst.j = 5;
ext2.basic_inst.j = 5;
ext3.basic_inst.j = 5;
ext4.basic_inst.j = 5;

myclass::override_with_copy("@%*",ext0,log1,`__FILE__, `__LINE__);
gen0.build_ph();
myclass::override_with_copy("@%*",ext1,log1,`__FILE__, `__LINE__);
gen1.build_ph();
myclass::override_with_copy("@%*",ext2,log1,`__FILE__, `__LINE__);
gen2.build_ph();
myclass::override_with_copy("@%*",ext3,log1,`__FILE__, `__LINE__);
gen3.build_ph();
myclass::override_with_copy("@%*",ext4,log1,`__FILE__, `__LINE__);
gen4.build_ph();
log1.report();
endfunction

endclass


initial
begin
env env10= new("env");
env10.build_ph();
end

endprogram
