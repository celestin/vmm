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
//  Filename: scenarios.sv
//  Date: 2 Nov 2009
//  Author: Doug Smith
//  Description:  Scenario library for the WB interface.
//
//////////////////////////////////////////////////////////////////////////////

`ifndef SCENARIOS_SV
`define SCENARIOS_SV

`include "wb_spi_trans.svh"

// Create a scenario generator using the wb_spi_trans
`vmm_scenario_gen( wb_spi_trans, "WB/SPI Scenarios" )


//-------------------------------------------------------------------------
//
// wb_op - Sequence to perform a WB operation (read or write)
//
//-------------------------------------------------------------------------
class wb_op_scn extends wb_spi_trans_scenario;

	rand bit [AWIDTH-1:0] my_addr;
	rand bit [DWIDTH-1:0] my_data;
	rand trans_t          my_kind;

	`vmm_typename ( wb_op_scn ) 

	function new();
		define_scenario( "wb_op_scn", 0 );
	endfunction

	virtual task apply( wb_spi_trans_channel channel,
			    ref int unsigned n_inst );

		wb_spi_trans	tr = new();

		if ( tr.randomize with { 
			addr == my_addr;
			data == my_data;
			kind == my_kind; 
		} ) begin
			tr.display();
			channel.put( tr );
			n_inst++;
		end
	endtask
endclass


//-------------------------------------------------------------------------
//
// wb_read - Scenario to perform a WB read transaction
//
//-------------------------------------------------------------------------
class wb_read_scn extends wb_op_scn;

	`vmm_typename ( wb_read_scn ) 

	function new();
		define_scenario( "wb_read_scn", 0 );
	endfunction

	constraint kind_c { my_kind == RX; }
endclass


//-------------------------------------------------------------------------
//
// wb_write - Scenario to perform a WB write transaction
//
//-------------------------------------------------------------------------
class wb_write_scn extends wb_op_scn;

	`vmm_typename ( wb_write_scn ) 

	function new();
		define_scenario( "wb_write_scn", 0 );
	endfunction

	constraint kind_c { my_kind == TX; }
endclass


//-------------------------------------------------------------------------
//
// wb_to_spi - Scenario to send data from the WB to the SPI interface.
//
//-------------------------------------------------------------------------
class wb_to_spi_scn extends wb_spi_trans_scenario;
	rand bit [3:0][DWIDTH-1:0] data;
	rand ctrl_t      ctrl;			// Controls DUT configuration
	rand divider_t   divider;
	rand ss_t        ss;
	wb_write_scn     wb_write = new();	// Instance of write scenario

	constraint divider_c {
	  divider[31:16] == 0;				// Reserved
	  divider[15: 0] inside { [ 0 : 100 ] };	// Reasonable clk freq
	}
	constraint ctrl_c {
	  // Configure control reg for SPI transfer (GO_BSY not set yet) 
	  ctrl[31:7] == ((A_SS_BIT | IE_BIT | LSB_BIT | TX_NEG | RX_NEG) >> 7 );
	}
	constraint ss_c { ss == '1; }		// Only one slave select 

	`vmm_typename ( wb_to_spi_scn ) 

	function new();
		define_scenario( "wb_to_spi_scn", 0 );
	endfunction

	virtual task apply( wb_spi_trans_channel channel,
			    ref int unsigned n_inst );

  		// Write data into the TX registers
	        wb_write.randomize with { my_addr == SPI_TX_RX0; 
					  my_data == data[0]; };
	        wb_write.apply( channel, n_inst );
  
  		if ( ctrl.char_len > 32 || ctrl.char_len == 0 ) begin

	           wb_write.randomize with { my_addr == SPI_TX_RX1; 	
					     my_data == data[1]; };
	           wb_write.apply( channel, n_inst );
		end

  		if ( ctrl.char_len > 64 || ctrl.char_len == 0 ) begin
	           wb_write.randomize with { my_addr == SPI_TX_RX2; 	
					     my_data == data[2]; };
	           wb_write.apply( channel, n_inst );
		end

  		if ( ctrl.char_len > 96 || ctrl.char_len == 0 ) begin
	           wb_write.randomize with { my_addr == SPI_TX_RX3; 	
					     my_data == data[3]; };
	           wb_write.apply( channel, n_inst );
		end
  
  		// Write the configuration registers
	        wb_write.randomize with { my_addr == SPI_DIVIDER; 	
					  my_data == divider; };
	        wb_write.apply( channel, n_inst );


	        wb_write.randomize with { my_addr == SPI_SS; 	
					  my_data == ss; };
	        wb_write.apply( channel, n_inst );
  
  		// Write to the control register but don't set the GO bit yet
	        wb_write.randomize with { my_addr == SPI_CTRL; 	
					  my_data == ctrl; };
	        wb_write.apply( channel, n_inst );
  
  		// Set the GO bit to perform the SPI transfer
		ctrl |= GO_BIT; 
	        wb_write.randomize with { my_addr == SPI_CTRL; 	
					  my_data == ctrl; };
	        wb_write.apply( channel, n_inst );
	endtask

	`vmm_class_factory( wb_to_spi_scn )
endclass


`endif	// SCENARIOS_SV
