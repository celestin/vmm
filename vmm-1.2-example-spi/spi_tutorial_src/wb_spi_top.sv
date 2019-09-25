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
//  Filename: wb_spi_top.sv
//  Date: 2 Nov 2009
//  Author: Doug Smith
//  Description:  Top VMM testbench module.
//
//////////////////////////////////////////////////////////////////////////////


program wb_spi_top;

   import wb_spi_pkg::*;			// Load in the testbench

   wb_spi_env 		e;
   wb_test1		t;
   dut_if_wrapper	i;

   //////////////////////////////////////
   // OK, now run the test
   //////////////////////////////////////
   initial
   begin
	// Create the environment
	e = new( "wb_spi_env", "e" );

	// Setup the DUT interface wrapper
	i = new( "dut_if_wrapper", wb_spi_tb.dut_if );
	vmm_opts::set_object( "dut_intf", i );

	// Tests
	t = new( "wb_test1", e );
	vmm_simulation::run_tests();	// Kick off VMM
   end

endprogram : wb_spi_top
