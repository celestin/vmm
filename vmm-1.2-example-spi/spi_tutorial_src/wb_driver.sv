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
//  Filename: wb_driver.sv
//  Date: 30 Oct 2009
//  Author: Doug Smith
//  Description:  Driver for the WB interface. 
//
//////////////////////////////////////////////////////////////////////////////

`ifndef WB_DRIVER_SV
`define WB_DRIVER_SV

`define dwidth 32
`define awidth 32

class wb_driver extends vmm_xactor; 

   virtual dut_intf.wb	 	dut_if;
   wb_spi_trans_channel		in_chan;

   `vmm_typename( wb_driver )

   ///////////////////////////////////////////
   // Constructor
   ///////////////////////////////////////////
   function new ( string name, string inst, vmm_group parent );
	super.new( name, inst,, parent );
   endfunction : new


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
   // main() task - do the work here
   ////////////////////////////////////////////////////////////////
   task main; 
     fork
      super.main();
      begin : main_fork
  	int numbits;
  
  	`vmm_note(log, "Starting the WB driver ..."); 
  
  	forever begin : forever_loop
  
  	   ///////////////////////////////////////////////////
  	   // Get the next sequence item to know what to do
  	   ///////////////////////////////////////////////////
  	   wb_spi_trans trans;
  
  	   `vmm_note( this.log, "Getting packet ...");
  	   in_chan.get( trans );
  
	   this.notify.reset(XACTOR_IDLE);
	   this.notify.indicate(XACTOR_BUSY);	// Don't end yet!

  	   `vmm_note( this.log, "Transmitting packet ...");
  	   trans.display();
  
  	   ///////////////////////////////////////////////////
  	   // Now, do the transaction and twiddle the bits
  	   ///////////////////////////////////////////////////
  	   if (trans.kind == RX) begin

    		// Read from the specific Wishbone register
		wb_read( trans.addr, trans.data );

  	   end 
  	   else begin
  		// Write to the specific Wishbone register
		wb_write( trans.addr, trans.data );
  
		// Wait for the SPI transfer to complete if GO_BIT set
		if ((trans.addr == SPI_CTRL) && (trans.data & GO_BIT))
		   @(posedge dut_if.wb_int_o);	// Wait for interrupt
  	   end

	   this.notify.reset(XACTOR_BUSY);
	   this.notify.indicate(XACTOR_IDLE);	// Ok, not busy
  	end : forever_loop
      end : main_fork
     join_none
   endtask : main


   /////////////////////////////
   // Wishbone write task
   /////////////////////////////
   task automatic wb_write(input int addr, input int data);
  
      `vmm_note( this.log, $psprintf("wb_write task: addr = %x, data = %x", addr, data));

      // wait initial delay
      @(posedge dut_if.wb_clk_i);
  
      // Drive Wishbone signal
      #1;
      dut_if.wb_adr_i  = addr;
      dut_if.wb_dat_i  = data;
      dut_if.wb_cyc_i  = 1'b1;
      dut_if.wb_stb_i  = 1'b1;
      dut_if.wb_we_i   = 1'b1;
      dut_if.wb_sel_i  = {`dwidth/8{1'b1}};
      @(posedge dut_if.wb_clk_i);
  
      // Wait for acknowledge
      while (~dut_if.wb_ack_o) @(posedge dut_if.wb_clk_i);
  
      // Release Wishbone signals
      #1;
      dut_if.wb_cyc_i  = 1'b0;
//      dut_if.wb_stb_i  = 1'bx;		// Uncomment these if you don't mind X
//      dut_if.wb_adr_i  = {`awidth{1'bx}};
//      dut_if.wb_dat_i  = {`dwidth{1'bx}};
//      dut_if.wb_we_i   = 1'hx;
//      dut_if.wb_sel_i  = {`dwidth/8{1'bx}};

   endtask			// wb_write()

  
   /////////////////////////////
   // Wishbone read cycle
   /////////////////////////////
   task automatic wb_read(input int addr, output int data);
  
      // wait initial delay
      @(posedge dut_if.wb_clk_i);
  
      // Drive Wishbone signals
      #1;
      dut_if.wb_adr_i  = addr;
      dut_if.wb_dat_i  = {`dwidth{1'bx}};
      dut_if.wb_cyc_i  = 1'b1;
      dut_if.wb_stb_i  = 1'b1;
      dut_if.wb_we_i   = 1'b0;
      dut_if.wb_sel_i  = {`dwidth/8{1'b1}};
      @(posedge dut_if.wb_clk_i);
  
      // Wait for acknowledge
      while(~dut_if.wb_ack_o) @(posedge dut_if.wb_clk_i);
  
      // Release Wishbone signals
      #1;
      dut_if.wb_cyc_i  = 1'b0;
//      dut_if.wb_stb_i  = 1'bx;	// Uncomment these if you don't mind X
//      dut_if.wb_adr_i  = {`awidth{1'bx}};
//      dut_if.wb_dat_i  = {`dwidth{1'bx}};
//      dut_if.wb_we_i   = 1'hx;
//      dut_if.wb_sel_i  = {`dwidth/8{1'bx}};
      data = dut_if.wb_dat_o;
      @(negedge dut_if.wb_ack_o);	// Find end of data transfer
  
      `vmm_note( this.log, $psprintf("wb_read task: addr = %x, data = %x", addr, data));

    endtask			// wb_read()

endclass : wb_driver


`endif	// WB_DRIVER_SV
