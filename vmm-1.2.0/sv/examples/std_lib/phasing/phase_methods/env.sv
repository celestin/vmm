program automatic test;
 `include "vmm.sv"

typedef class myunit;

class myunit extends vmm_unit;
`vmm_typename(myunit)

extern virtual function void build_ph();
extern virtual function void start_of_sim_ph();
extern virtual task reset_ph(); 
extern virtual task config_dut_ph();
extern virtual task start_ph();
extern function void destruct_ph();
vmm_timeline  tml;
function new (string name, string inst, vmm_unit parent=null);
  super.new(name,inst,parent);
endfunction
endclass

//Methods Definations
function void myunit::build_ph();
  vmm_phase     ph;
  vmm_unit_startsimph_phase_def startph = new;
  tml = this.get_timeline();
		
  `vmm_note(log,"**** Executing build phase ....\n");
		
  `vmm_note(log, {tml.get_object_name(), " is being used.\n "});
		
		/* Inserting some UDF phase */
		tml.insert_phase("UDF", "reset", startph); 
  ph = tml.get_phase("UDF");
  `vmm_note(log, {ph.get_object_name()," was inserted successfully."});
		
		/* Checking the previous and the next phase of UDF */ 
  `vmm_note(log,{tml.get_previous_phase_name("UDF")," is the phase prior to UDF ...\n"});		
  `vmm_note(log,{tml.get_next_phase_name("UDF")," is phase next to UDF ...\n"});		

endfunction:build_ph 

function void myunit::start_of_sim_ph();
  `vmm_note(log,"**** Executing start_of_sim phase ....\n");
endfunction:start_of_sim_ph

task myunit::reset_ph(); 
#10;
  `vmm_note(log,"**** Executing reset phase ....\n");
endtask:reset_ph 

task myunit::config_dut_ph(); 
#5;
  `vmm_note(log,"**** Executing configure dut phase ....\n");
endtask:config_dut_ph 

task myunit::start_ph(); 
  #15;
  `vmm_note(log,"**** Executing start phase ....\n");
endtask:start_ph 

function void myunit::destruct_ph(); 
  `vmm_note(log,"**** Reached destruct phase ....\n***** RUN COMPLETED ******\n");
endfunction:destruct_ph 

class mytest extends vmm_test;
`vmm_typename(mytest)

  vmm_timeline       topTimeline;
  myunit             topUnit;
  function new (string name, string inst, vmm_unit parent=null);
    super.new(name,inst,parent);
    topTimeline = new("tlt", "topTimeline", this);
    topUnit = new("tlm","topUnit", topTimeline);
  endfunction

endclass

vmm_log log = new("Test", "main");

mytest test;

initial begin
  test = new("test", "test"); 
  //run the phases in timeline
		
  test.topTimeline.step_function_phase("rtl_config");
  test.topTimeline.step_function_phase("build");
		
		/* Calling run_phase() will not execute rtl_config and build now ...
     but will start the execution from configure()  */
  `vmm_note(log,"Calling run_phase() ......\n");
		fork 
  begin 
		 test.topTimeline.run_phase(); 
		end
		begin
		 #5;
		 if(test.topTimeline.task_phase_timeout("reset",2) == 1) begin
    `vmm_note(log,"Timer expired for 'reset' hence Aborting the reset phase ....\n");		
    test.topTimeline.abort_phase("reset"); //// Aborting the reset phase
			end		
		end	
		join
	 `vmm_note(log,"Resetting to the `start_of_sim' phase \nExpecting the execution of reset phase this time...\n");
  test.topTimeline.task_phase_timeout("reset",15); /// Increasing the timeout limit as it takes more than 
  test.topTimeline.reset_to_phase("start_of_sim");
  fork 
		begin
    test.topTimeline.run_phase(); 
		end
		begin
		 #25;
			/*... If start_phase timer expires jump to destruct phase ...
			  jump_to_phase will abort the current phase and jump to destruct */
		 if(test.topTimeline.task_phase_timeout("start",2) == 1) begin
    `vmm_note(log,"Timer expired for 'start' hence jumping to the destruct phase ....\n");		
    test.topTimeline.jump_to_phase("destruct");
			end		
		end
		join

  log.report();
end
endprogram
