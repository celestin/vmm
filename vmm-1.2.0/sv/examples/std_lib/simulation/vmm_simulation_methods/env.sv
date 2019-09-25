program test;

`include "vmm.sv"

class vip1 extends vmm_unit;
`vmm_typename(vip1)

  function new(string inst, vmm_unit parent = null);
    super.new(get_typename(), inst, parent);
  endfunction
		
  virtual function void udf_start_ph();
    `vmm_note(log,"UDF :: Executing the User defined start phase ...");
  endfunction
		
  virtual task udf_start_sub_ph();
    `vmm_note(log,"UDF :: Executing the User defined start_sub phase ...");
  endtask

  virtual function void configure_ph();
    `vmm_note(log, "Configuring phase..\n");
  endfunction
		
  virtual function void connect_ph();
    `vmm_note(log, "Connect phase done \n");
  endfunction

endclass

class vip2 extends vmm_unit;
`vmm_typename(vip2)

  function new(string inst, vmm_unit parent = null);
    super.new(get_typename(), inst, parent);
  endfunction
		
  virtual task udf_stop_ph();
    `vmm_note(log,"UDF :: Executing the User defined stop phase ...");
  endtask

  virtual task udf_stop_sub_ph();
    `vmm_note(log,"UDF :: Executing the User defined stop_sub phase ...");
  endtask

  virtual task run_ph();
    `vmm_note(log, "Run_phase done... \n");
  endtask
		
  virtual function void report_ph();
    `vmm_note(log, "Report phase done ... \n");
  endfunction

endclass

class my_env extends vmm_unit;
`vmm_typename(my_env)
  vip1 v1;
  vip2 v2;
  
  function new(string inst, vmm_unit parent = null);
    super.new(get_typename(), inst, parent);
  endfunction

  virtual function void build_ph();
     v1 = new("v1", this);
     v2 = new("v2", this);
  endfunction

endclass

class my_test extends vmm_test;
`vmm_typename(my_test)
  
  function new();
     super.new(get_typename(), "test");
  endfunction
		
  virtual function void start_of_sim_ph();
    `vmm_note(log, "start_of_sim phase done \n");
     vmm_simulation::display_phases();
  endfunction

		
  virtual function void destruct_ph();
    `vmm_note(log, "Destruct phase done \n");
  endfunction

endclass

/*.............. VIP1 ...........................................*/

class udf_start_def extends vmm_fork_task_phase_def #(vip1);
  `vmm_typename(udf_start_def)
   extern virtual task do_task_phase(vip1 obj);
endclass:udf_start_def

task udf_start_def::do_task_phase(vip1 obj);
 if(obj.is_enabled())
     obj.udf_start_ph();
endtask:do_task_phase

class udf_start_sub_def extends vmm_fork_task_phase_def #(vip1);
   `vmm_typename(udf_start_sub_def)

   extern virtual task do_task_phase(vip1 obj);
endclass:udf_start_sub_def

task udf_start_sub_def::do_task_phase(vip1 obj);
 if(obj.is_enabled())
     obj.udf_start_sub_ph();
endtask:do_task_phase

/*....................VIP2 .....................................*/

class udf_stop_def extends vmm_fork_task_phase_def #(vip2);
   `vmm_typename(udf_stop_def)

   extern virtual task do_task_phase(vip2 obj);
endclass:udf_stop_def

task udf_stop_def::do_task_phase(vip2 obj);
 if(obj.is_enabled())
     obj.udf_stop_ph();
endtask:do_task_phase

class udf_stop_sub_def extends vmm_fork_task_phase_def #(vip2);
   `vmm_typename(udf_stop_sub_def)

   extern virtual task do_task_phase(vip2 obj);
endclass:udf_stop_sub_def

task udf_stop_sub_def::do_task_phase(vip2 obj);
 if(obj.is_enabled())
     obj.udf_stop_sub_ph();
endtask:do_task_phase

/*.........................................................*/

my_test test;
vmm_simulation vmm_sim;
vmm_timeline   tlm;
vmm_log log; 
udf_start_def start_def;
udf_start_sub_def start_sub_def;
my_env env;
udf_stop_def stop_def;
udf_stop_sub_def stop_sub_def;

initial begin
   start_def = new; 
   start_sub_def = new;
   stop_def = new; 
   stop_sub_def = new;
   
			log = new("test","snps_test");
   test = new();
   env = new("env");			
			
   vmm_sim = vmm_simulation::get_sim();
			`vmm_note(log, {vmm_sim.get_object_name()," is being used."});
   tlm = vmm_simulation::get_top();
			`vmm_note(log, {tlm.get_object_name()," is the top-level test timeline.\n"});

/********************		PRE_TEST *****************************/
			`vmm_note(log, "Inserting start_def_phase before pre-test configure phase ....\n");
   vmm_simulation::allow_new_phases();/// allow_new_phase is must to ensure the insertion
   vmm_simulation::insert_pre_test_phase("start_def_ph","configure",start_def);
		
 	`vmm_note(log, "\nAdding start_sub_def phase to connect phase ....\n");
   vmm_simulation::allow_new_phases();/// allow_new_phase is must to ensure the addition
   vmm_simulation::add_pre_test_phase("connect",start_sub_def);
		 
/********************		POST_TEST *****************************/
			`vmm_note(log, "Inserting stop_def_phase before post-test report phase ....\n");
   vmm_simulation::allow_new_phases();/// allow_new_phase is must to ensure the insertion
   vmm_simulation::insert_post_test_phase("stop_def_ph","report",stop_def);
		
 	`vmm_note(log, "\nAdding stop_sub_def phase to report phase ....\n");
   vmm_simulation::allow_new_phases();/// allow_new_phase is must to ensure the addition
   vmm_simulation::add_post_test_phase("report",stop_sub_def);

/********************		LIST & RUN TESTS *****************************/

   vmm_simulation::list();
   vmm_simulation::run_tests();

end
endprogram



