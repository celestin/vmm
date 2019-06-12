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

program test;

`include "vmm.sv"

class vip1 extends vmm_group;
`vmm_typename(vip1)

  function new(string inst, vmm_group parent = null);
    super.new(get_typename(), inst, parent);
  endfunction
		
  virtual function void configure_ph();
    `vmm_note(log, "Configuring phase..\n");
  endfunction
		
  virtual function void connect_ph();
    `vmm_note(log, "Connect phase done \n");
  endfunction

endclass

class vip2 extends vmm_group;
`vmm_typename(vip2)

  function new(string inst, vmm_group parent = null);
    super.new(get_typename(), inst, parent);
  endfunction
		
  virtual task run_ph();
    `vmm_note(log, "Run_phase done... \n");
  endtask
		
  virtual function void report_ph();
    `vmm_note(log, "Report phase done ... \n");
  endfunction

endclass

class my_env extends vmm_group;
`vmm_typename(my_env)
  vip1 v1;
  vip2 v2;
  
  function new(string inst, vmm_group parent = null);
    super.new(get_typename(), inst, parent);
  endfunction

  virtual function void build_ph();
     v1 = new("v1", this);
     v2 = new("v2", this);
  endfunction

endclass

class my_test extends vmm_test;
`vmm_typename(my_test)
  
  function new(string name);
     super.new(name);
  endfunction
		
  virtual function void configure_test_ph();
     vmm_simulation::display_phases();
     `vmm_note(log, "configure_test phase done \n");
  endfunction

  virtual function void start_of_sim_ph();
    `vmm_note(log, "start_of_sim phase done \n");
  endfunction

		
endclass

/*.............. VIP1 ...........................................*/

/*....................VIP2 .....................................*/

/*.........................................................*/

my_test test;
vmm_simulation vmm_sim;
vmm_timeline   tlm;
vmm_log log; 
my_env env;

initial begin

   log = new("test","snps_test");
   test = new("test1");
   env = new("env");			
			
   vmm_sim = vmm_simulation::get_sim();
   `vmm_note(log, {vmm_sim.get_object_name()," is being used."});
/********************		PRE_TEST *****************************/
		 
   tlm = vmm_simulation::get_pre_timeline();
			`vmm_note(log, {tlm.get_object_name()," is the pre test timeline.\n"});
/********************		TOP_TEST *****************************/
   tlm = vmm_simulation::get_top_timeline();
			`vmm_note(log, {tlm.get_object_name()," is the top-level test timeline.\n"});

/********************		POST_TEST *****************************/
   tlm = vmm_simulation::get_post_timeline();
			`vmm_note(log, {tlm.get_object_name()," is the post test timeline.\n"});
/********************		LIST & RUN TESTS *****************************/

   vmm_simulation::list();
   vmm_simulation::run_tests();

end
endprogram



