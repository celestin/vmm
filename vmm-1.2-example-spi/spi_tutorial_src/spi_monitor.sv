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
//  Filename: spi_monitor.sv
//  Date: 30 Oct 2009
//  Author: Doug Smith
//  Description:  Monitor for the SPI interface.
//
//////////////////////////////////////////////////////////////////////////////

`ifndef SPI_MONITOR_SV
`define SPI_MONITOR_SV


class spi_monitor extends vmm_xactor;

   // Interface to the SPI DUT interface
   virtual dut_intf.spi dut_if;

   // Communication ports
   vmm_tlm_analysis_port #( spi_monitor, mon_sb_trans ) sb_ap;	// To scoreboard

   ///////////////////////////////////////////
   // Constructor
   ///////////////////////////////////////////
   function new ( string name, string inst, vmm_group parent );
	super.new( name, inst,, parent );
   endfunction : new


   ///////////////////////////////////////////
   // Build phase
   ///////////////////////////////////////////
   function void build_ph();
	super.build_ph();
	sb_ap = new ( this, "Analysis port to scoreboard" );
   endfunction : build_ph


   ///////////////////////////////////////////
   // Connect phase
   ///////////////////////////////////////////
   function void connect_ph();
	bit is_set;
	dut_if_wrapper	if_wrp;

	// Grab the interface wrapper for the virtual interface 
	if ( $cast( if_wrp, vmm_opts::get_object_obj( is_set, 
					this, "dut_intf" ))) begin
		if ( if_wrp != null )
			this.dut_if = if_wrp.dut_if;
		else
			`vmm_fatal( log, "Cannot find DUT interface!!" );
	end
   endfunction : connect_ph


   ///////////////////////////////////////////
   // Start of simulation phase
   ///////////////////////////////////////////
   function void start_of_sim_ph();
	if ( dut_if == null)
		`vmm_fatal( log, "Virtual interface not connected!" );
   endfunction


   ////////////////////////////////////////////////////////////////
   // main() body
   ////////////////////////////////////////////////////////////////
   task main();	
     fork
      super.main();
      begin : main_fork

	`vmm_note( this.log, "Monitoring the SPI bus ..." );

	forever begin
	   bit [6:0] i = 0;
	   mon_sb_trans trans = new;		// New transaction

	   wait ( ~dut_if.ss_pad_o );		// Wait for a tx to begin

	   this.notify.reset(XACTOR_IDLE);
	   this.notify.indicate(XACTOR_BUSY);	// Don't end yet!


	   `vmm_note( this.log, "SPI bus ready to transmit...");

	   fork
		begin
		   for ( i = 0; ~dut_if.ss_pad_o[0]; i++ ) begin
			   @(posedge dut_if.sclk_pad_o);
			   trans.data[i] = dut_if.mosi_pad_o;
		   end
		end
		wait ( dut_if.ss_pad_o[0] );	// Transfer finished
	   join_any
	   disable fork;

	   //
	   // Send the transaction to the scoreboard.
	   //
	   if ( i ) begin		// Make sure something was transferred
		`vmm_note( this.log, "Sending transaction to scoreboard..." );
	   	trans.display();
	   	sb_ap.write( trans );
	   end

	   this.notify.reset(XACTOR_BUSY);
	   this.notify.indicate(XACTOR_IDLE);	// Ok, not busy
	end

      end : main_fork
     join_none
   endtask : main

endclass : spi_monitor


`endif	// SPI_MONITOR_SV
