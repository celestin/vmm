//////////////////////////////////////////////////////////////////////////////
//
//  DDDDD   OOO  UU UU LL    OOO   SSS
//  DD  DD OO OO UU UU LL   OO OO SS  S
//  DD  DD OO OO UU UU LL   OO OO  SS
//  DD  DD OO OO UU UU LL   OO OO   SS
//  DD  DD OO OO UU UU LL   OO OO S  SS
//  DDDDD   OOO   UUU  LLLL  OOO   SSS
//
//  Doulos
//
//  Filename: wb_test1.sv
//  Date: 2 Nov 2009
//  Author: Doug Smith
//  Description:  A simple testcase.
//
//////////////////////////////////////////////////////////////////////////////

`ifndef WB_TEST1_SV
`define WB_TEST1_SV

class wb_test1 extends vmm_test;

	`vmm_typename( wb_test1 )

 	wb_spi_env my_env;

	function new(string name, wb_spi_env my_env);
		super.new(name);
		this.my_env = my_env;
	endfunction

	function void start_of_sim_ph;
		//vmm_timeline t = this.get_timeline();
		//t.task_phase_timeout( "run_test", 500 );  // Time-out on the run phase

		//  Register test scenario with scenario generator
//		begin
			wb_to_spi_scn	scn = new();

			// Remove the atomic scenario
			my_env.wb_sub.scn_gen.scenario_set.delete();			
			// Register test scenario
			my_env.wb_sub.scn_gen.register_scenario( "wb_to_spi", scn );
			// Specify number of scenarios to run
			vmm_opts::set_int("num_scenarios", 1, this);

//		end
	endfunction


	// Wait until the scenario generator is finished
	virtual task shutdown_ph();
		my_env.wb_sub.scn_gen.notify.wait_for(wb_spi_trans_scenario_gen::DONE);
	endtask

endclass : wb_test1

`endif	// WB_TEST1_SV
