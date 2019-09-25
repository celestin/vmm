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
//  Filename: dut_intr.sv
//  Date: 30 Oct 2009
//  Author: Doug Smith
//  Description:  File to define the interface used on the DUT.
//
//////////////////////////////////////////////////////////////////////////////

`ifndef DUT_INTF_SV
`define DUT_INTF_SV


`include "spi_defines.v"
interface dut_intf;

     // Wishbone signals
     logic                  wb_clk_i;         // master clock input
     logic                  wb_rst_i;         // sync active high reset
     logic            [4:0] wb_adr_i;         // lower address bits
     logic         [32-1:0] wb_dat_i;         // databus input
     logic         [32-1:0] wb_dat_o;         // databus output
     logic            [3:0] wb_sel_i;         // byte select inputs
     logic                  wb_we_i;          // write enable input
     logic                  wb_stb_i;         // stobe/core select signal
     logic                  wb_cyc_i;         // valid bus cycle input
     logic                  wb_ack_o;         // bus cycle ack output
     logic                  wb_err_o;         // termination w/ error
     logic                  wb_int_o;         // int req signal output
                                           
     // SPI signals                                     
     logic [`SPI_SS_NB-1:0] ss_pad_o;         // slave select
     logic                  sclk_pad_o;       // serial clock
     logic                  mosi_pad_o;       // master out slave in
     logic                  miso_pad_i;       // master in slave out

     // Wishbone signals
     modport wb (output wb_clk_i, wb_rst_i, wb_adr_i, wb_dat_i, 
		       wb_sel_i, wb_we_i, wb_stb_i, wb_cyc_i, 
		 input wb_dat_o, wb_ack_o, wb_err_o, wb_int_o);

     // SPI signals
     modport spi (output miso_pad_i, input ss_pad_o, sclk_pad_o, mosi_pad_o);

     // Note: modports are used by the testbench so directions are with
     // respect to the testbench.

endinterface

`endif	// DUT_INTF_SV
