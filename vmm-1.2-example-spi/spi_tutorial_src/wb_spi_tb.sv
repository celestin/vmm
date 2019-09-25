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
//  Filename: wb_spi_tb.sv
//  Date: 2 Nov 2009
//  Author: Doug Smith
//  Description:  Top VMM testbench module.
//
//////////////////////////////////////////////////////////////////////////////


module wb_spi_tb;

   import wb_spi_pkg::*;			// Load in the testbench

   localparam	PERIOD = 10;

   dut_intf dut_if();				// Instantiate the bus

   /////////////////////////////////////////////////////////////////////////
   // Instantiate the DUT.
   /////////////////////////////////////////////////////////////////////////
   spi_wrapper dut1 ( .dut_if( dut_if ) );


   //////////////////////////////////////
   // Clock generation
   //////////////////////////////////////
   always
   begin
	dut_if.wb_clk_i = 0;
	#(PERIOD/2);
	dut_if.wb_clk_i = 1;
	#(PERIOD/2);
   end

endmodule : wb_spi_tb
