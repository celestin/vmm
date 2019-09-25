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
//  Filename: wb_subenv.sv
//  Date: 30 Oct 2009
//  Author: Doug Smith
//  Description:  Subenvironment structure to house the WB monitor, driver, and
//		  scenario generator.
//
//////////////////////////////////////////////////////////////////////////////

`ifndef WB_SUBENV_SV
`define WB_SUBENV_SV

////////////////////////////////////////////////////////////////////////////
// Must create subenv from vmm_group to use implicit phasing; otherwise,
// the subcomponents do not get phased correctly.  
// See VMM 1.2 User Guide, "Modeling Transactors and Timelines" > 
// 	"Transactor Phasing" > "Implicit Phasing"
////////////////////////////////////////////////////////////////////////////

class wb_subenv extends vmm_group; 

   wb_monitor   		wb_mon;
   wb_driver    		wb_drv;
   wb_spi_trans_scenario_gen	scn_gen;
   wb_spi_trans_channel		gen_to_drv_chan;
   int				num_scenarios;

   `vmm_typename( wb_subenv )

   // Configuration mechanism for controlling the number of scenarios
   `vmm_unit_config_begin( wb_subenv )
	`vmm_unit_config_rand_int( num_scenarios, 5, "Number of scenarios to run", 0, "DO_ALL" )
   `vmm_unit_config_end( wb_subenv )


   ///////////////////////////////////////////
   // Constructor
   ///////////////////////////////////////////
   function new ( string name, string inst, vmm_group parent );
	super.new ( "wb_subenv", inst, parent );
   endfunction : new


   ///////////////////////////////////////////
   // Build phase
   ///////////////////////////////////////////
   function void build_ph();
	super.build_ph();

	`vmm_note( this.log, "Creating subenvironment ..." );
	gen_to_drv_chan = new( "gen_to_drv_chan", " Channel" );
	wb_drv 		= new( "wb_driver", "wb_drv", this );
	wb_mon 		= new( "wb_monitor", "wb_mon", this );
	scn_gen 	= new( "scn_gen", 0 );
   endfunction : build_ph


   ///////////////////////////////////////
   // Connect phase
   ///////////////////////////////////////
   function void connect_ph();
	// Connect up the channel between the generator and the driver
	wb_drv.in_chan = gen_to_drv_chan;
	scn_gen.out_chan = gen_to_drv_chan;

	// Register end-of-test consensus
	vote.register_xactor( wb_drv );
	vote.register_xactor( wb_mon );
	vote.register_xactor( scn_gen );
	vote.register_channel( gen_to_drv_chan );
   endfunction : connect_ph


   ////////////////////////////////////////////////////////////////
   // Start the stimulus generator phase 
   ////////////////////////////////////////////////////////////////
   function void start_of_sim_ph();
	super.start_of_sim_ph();

	// Start the scenario generator
	scn_gen.stop_after_n_scenarios = num_scenarios;
	scn_gen.start_xactor();		// Testcase should register scenario to run
   endfunction


   ////////////////////////////////////////////////////////////////
   // Shutdown phase 
   ////////////////////////////////////////////////////////////////
   task shutdown_ph();
	scn_gen.notify.wait_for(wb_spi_trans_scenario_gen::DONE);
	`vmm_note( this.log, "Scenario generation done..." );

	// Stop the scenario generator
	scn_gen.stop_xactor();
   endtask

endclass : wb_subenv


`endif	// WB_SUBENV_SV
