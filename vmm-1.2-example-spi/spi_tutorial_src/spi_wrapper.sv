//////////////////////////////////////////////////////////////////////////////
//
//  DDDDD   OOO  UU UU LL    OOO   SSS
//  DD  DD OO OO UU UU LL   OO OO SS  S
//  DD  DD OO OO UU UU LL   OO OO  SS
//  DD  DD OO OO UU UU LL   OO OO   SS
//  DD  DD OO OO UU UU LL   OO OO S  SS
//  DDDDD   OOO   UUU  LLLL  OOO   SS
//
//  Doulos
//
//  Filename: spi_wrapper.sv
//  Date: 2 Nov 2009
//  Author: Doug Smith
//  Description:  Top level wrapper around the DUT so interfaces can
//		  be used between the DUT and the testbench.
//
//////////////////////////////////////////////////////////////////////////////

module spi_wrapper (
	interface dut_if
);

   // Instantiate and connect up the DUT
   spi_top spi (   // Wishbone interface
   		.wb_clk_i(dut_if.wb_clk_i),
   		.wb_rst_i(dut_if.wb_rst_i),
   		.wb_adr_i(dut_if.wb_adr_i),
   		.wb_dat_i(dut_if.wb_dat_i),
   		.wb_dat_o(dut_if.wb_dat_o),
   		.wb_sel_i(dut_if.wb_sel_i),
   		.wb_we_i (dut_if.wb_we_i ),
   		.wb_stb_i(dut_if.wb_stb_i),
   		.wb_cyc_i(dut_if.wb_cyc_i),
   		.wb_ack_o(dut_if.wb_ack_o),
   		.wb_err_o(dut_if.wb_err_o),
   		.wb_int_o(dut_if.wb_int_o),
   	
   
   		// SPI signals
   		.ss_pad_o  (dut_if.ss_pad_o  ),
   		.sclk_pad_o(dut_if.sclk_pad_o),
   		.mosi_pad_o(dut_if.mosi_pad_o),
   		.miso_pad_i(dut_if.miso_pad_i)
   );
   
endmodule
