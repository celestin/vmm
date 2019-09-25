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
//  Filename: wb_spi_env.sv
//  Date: 30 Oct 2009
//  Author: Doug Smith
//  Description:  Testbench environment for testing the SPI DUT.
//
//////////////////////////////////////////////////////////////////////////////

`ifndef WB_SPI_ENV_SV
`define WB_SPI_ENV_SV

class wb_spi_env extends vmm_group;

   virtual dut_intf	 dut_if;
   wb_subenv		wb_sub;
   spi_monitor		spi_mon;
   wb_spi_scoreboard	wb_spi_sb;

   `vmm_typename( wb_spi_env )

   ///////////////////////////////////////////
   // Constructor
   ///////////////////////////////////////////
   function new ( string name, string inst, vmm_group parent = null );
	super.new( name, inst, parent );
   endfunction : new


   ///////////////////////////////////////
   // Build the member objects
   ///////////////////////////////////////
   function void build_ph();
	super.build_ph();

	// Create the WB subenvironment
	wb_sub = new( "wb_subenv", "wb_sub", this );

	// Create the SPI monitor
	spi_mon = new( "spi_monitor", "spi_mon", this );

	// Create the scoreboard
	wb_spi_sb = new( "wb_spi_sb" );

	`vmm_note( this.log, "Built wb_spi_env ..." );
   endfunction : build_ph


   ///////////////////////////////////////
   // Connect everything together
   ///////////////////////////////////////
   function void connect_ph();
	bit is_set;
	dut_if_wrapper	if_wrp;

	`vmm_note( this.log, "Connect phase... " );

	// Grab the interface wrapper for the virtual interface 
	if ( $cast( if_wrp, vmm_opts::get_object_obj( is_set, 
					this, "dut_intf" ))) begin
		if ( if_wrp != null )
			this.dut_if = if_wrp.dut_if;
		else
			`vmm_fatal( log, "Cannot find DUT interface!!" );
	end

	// Hook up the monitors to the scoreboard
	wb_sub.wb_mon.sb_ap.tlm_bind( wb_spi_sb.exp_ap );
	spi_mon.sb_ap.tlm_bind( wb_spi_sb.inp_ap );

	// Add monitor to end-of-test consensus
	vote.register_xactor( spi_mon );
   endfunction : connect_ph


   ///////////////////////////////////////////
   // Start of simulation phase
   ///////////////////////////////////////////
   function void start_of_sim_ph();
	if ( dut_if == null)
		`vmm_fatal( log, "Virtual interface not connected!" );
   endfunction


   ///////////////////////////////////////
   // Reset the DUT
   ///////////////////////////////////////
   task reset_ph();
	super.reset_ph();

	// Initial values
	`vmm_note( this.log, "Reseting the DUT ... " );
	dut_if.wb_adr_i  = {AWIDTH{1'bx}};
	dut_if.wb_dat_i  = {DWIDTH{1'bx}};
	dut_if.wb_cyc_i  = 1'b0;
	dut_if.wb_stb_i  = 1'bx;
	dut_if.wb_we_i   = 1'hx;
	dut_if.wb_sel_i  = {DWIDTH/8{1'bx}};

	// Reset the DUT
	dut_if.wb_rst_i = 0;
	#20;
	dut_if.wb_rst_i = 1;
	#200;
	dut_if.wb_rst_i = 0;
	#20;
	`vmm_note( this.log, "The DUT is now reset." );
   endtask : reset_ph

endclass : wb_spi_env

`endif	// WB_SPI_ENV_SV
