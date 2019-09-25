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
//  Filename: wb_monitor.sv
//  Date: 30 Oct 2009
//  Author: Doug Smith
//  Description:  Monitor for the WB interface.
//
//////////////////////////////////////////////////////////////////////////////

`ifndef WB_MONITOR_SV
`define WB_MONITOR_SV


class wb_monitor extends vmm_xactor; 

   // Interface to the WB DUT interface
   virtual dut_intf.wb	 	dut_if;

   // Communication ports
   vmm_tlm_analysis_port #( wb_monitor, mon_sb_trans ) sb_ap;

   mon_sb_trans			trans = new;

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
	`vmm_note( this.log, "Building analysis port..." );
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
   task main; 
     fork
       super.main();
       begin : main_fork
	  int numbits;

	  // Debug info
	  `vmm_note( this.log, "Monitoring the WB bus");

	  ///////////////////////////////////////////////////
	  // Monitor the bus
	  ///////////////////////////////////////////////////
	  forever begin : monitor_bus

		// Wait for a transaction to occur
		@(posedge dut_if.wb_cyc_i);		// Start of everything

	   	this.notify.reset(XACTOR_IDLE);
	   	this.notify.indicate(XACTOR_BUSY);	// Don't end yet!

		while (~dut_if.wb_stb_i) @(posedge dut_if.wb_clk_i);

		// Wait for an acknowledgement to sample valid data
     		while (~dut_if.wb_ack_o) @(posedge dut_if.wb_clk_i);

		while (dut_if.wb_ack_o) begin : wb_ack

		   logic [31:0] tmp_dat;

		   // Exit if transaction canceled
		   if (dut_if.wb_cyc_i !== 1 || dut_if.wb_stb_i !== 1) break;

		   // Figure out the kind of transaction
		   if (dut_if.wb_we_i === 1'b1) begin
			trans.kind = TX;
			tmp_dat = dut_if.wb_dat_i;
		   end
		   else if (dut_if.wb_we_i === 1'b0) begin
			trans.kind = RX;
			tmp_dat = dut_if.wb_dat_o;
		   end
		   else 
			`vmm_note( this.log, $psprintf("wb_we_i signal is %v", dut_if.wb_we_i));
	

		   // Capture only valid data transactions
		   trans.addr = dut_if.wb_adr_i;
		   case ( trans.addr )
			
		  	// Capture the data
			SPI_TX_RX0:	trans.data[31:0] = tmp_dat;
			SPI_TX_RX1:	trans.data[63:32] = tmp_dat;
			SPI_TX_RX2:	trans.data[95:64] = tmp_dat;
			SPI_TX_RX3:	trans.data[127:96] = tmp_dat;
			SPI_SS:		;
			SPI_DIVIDER:	;
			SPI_CTRL:	trans.ctrl = tmp_dat;
			default:	trans.addr = 'h1f;     // invalid addr
		   endcase

		   
		   // Now respond to the transaction and collect coverage
		   if (trans.addr != 'h1f) begin


		   	`vmm_note( this.log, $psprintf("addr = %8x, data = %8x", trans.addr, tmp_dat));
		   end else
		   	`vmm_note( this.log, $psprintf("Invalid address!  addr = %8x, data = %8x", dut_if.wb_adr_i, tmp_dat));


		   // Send to scoreboard when transaction totally sent
		   if ((trans.kind == TX) && (trans.addr == SPI_CTRL) && 
		       (trans.ctrl & GO_BIT)) begin
			`vmm_note( this.log, "Sending transaction to scoreboard..." );

			// Send to the scoreboard
			trans.display();
		   	trans.sample_cov();			// Sample the coverage
			sb_ap.write( trans );

			trans = new;		// Prepare for next transaction
		   end

		   // Next cycle
 		   @(posedge dut_if.wb_clk_i);

		end : wb_ack

	   	this.notify.reset(XACTOR_BUSY);
	        this.notify.indicate(XACTOR_IDLE);	// Ok, not busy
	  end : monitor_bus
       end : main_fork
     join_none
   endtask : main

endclass : wb_monitor


`endif	// WB_MONITOR_SV
