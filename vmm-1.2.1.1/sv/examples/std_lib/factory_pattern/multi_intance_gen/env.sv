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

class gen extends vmm_group;
`vmm_typename(gen)
	myclass tr;
	vmm_log log = new("cl","cl");

	virtual task config_dut_ph();
	tr = myclass::create_instance(this,"mydummyclass", `__FILE__,`__LINE__);
	`vmm_note(log,$psprintf("new Transction type is **** %d %s", tr.basic_inst.j,tr.get_typename()));
	tr.mytask;
	if(!((tr.i== 3) && (tr.basic_inst.j == 5)))
	`vmm_error(log,"ERROR");
	endtask

	function new (string name, string instance, vmm_group parent = null);
	super.new(get_typename(), instance, parent);
	endfunction

endclass


class env extends vmm_group;
`vmm_typename(env)
gen gen0 ;
gen gen1 ;
gen gen2 ;
gen gen3 ;
gen gen4 ;
ext ext0 ;
ext ext1 ;
ext ext2 ;
ext ext3 ;
ext ext4 ;

vmm_log log1 = new("cl1","cl1");

function new(string name, string instance, vmm_group parent = null);
super.new(get_typename(), instance, parent);
gen0 = new("gen0", "gen0", this);
gen1 = new("gen1", "gen1", this);
gen2 = new("gen2", "gen2", this);
gen3 = new("gen3", "gen3", this);
gen4 = new("gen4", "gen4", this);
ext0 = new();
ext1 = new();
ext2 = new();
ext3 = new();
ext4 = new();
endfunction

virtual function void build_ph();

ext0.basic_inst.j = 5;
ext1.basic_inst.j = 5;
ext2.basic_inst.j = 5;
ext3.basic_inst.j = 5;
ext4.basic_inst.j = 5;

endfunction

virtual function void start_of_sim_ph();
myclass::override_with_copy("@%*",ext0,log1,`__FILE__, `__LINE__);
myclass::override_with_copy("@%*",ext1,log1,`__FILE__, `__LINE__);
myclass::override_with_copy("@%*",ext2,log1,`__FILE__, `__LINE__);
myclass::override_with_copy("@%*",ext3,log1,`__FILE__, `__LINE__);
myclass::override_with_copy("@%*",ext4,log1,`__FILE__, `__LINE__);
log1.report();
endfunction

endclass


initial
begin
vmm_timeline topTimeline = new ("topTimeline", "topTimeline");
env env10= new("env", "env", topTimeline);
topTimeline.run_phase();
end

endprogram
