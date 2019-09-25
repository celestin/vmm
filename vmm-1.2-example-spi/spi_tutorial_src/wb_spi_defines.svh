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
//  Filename: wb_spi_defines.svh
//  Date: 2 Nov 2009
//  Author: Doug Smith
//  Description:  Contains constants for the WB interface register address map.
//
//////////////////////////////////////////////////////////////////////////////

`ifndef WB_SPI_DEFINES_SVH
`define WB_SPI_DEFINES_SVH


parameter SPI_TX_RX0 = 0;
parameter SPI_TX_RX1 = 4;
parameter SPI_TX_RX2 = 8;
parameter SPI_TX_RX3 = 'hc;
parameter SPI_CTRL = 'h10;
parameter SPI_DIVIDER = 'h14;
parameter SPI_SS = 'h18;
parameter GO_BIT = 'h100;
parameter RX_NEG = 'h200;
parameter TX_NEG = 'h400;
parameter LSB_BIT = 'h800;
parameter IE_BIT = 'h1000;
parameter A_SS_BIT = 'h2000;
parameter DWIDTH = 32;
parameter AWIDTH = 5;

`endif		// WB_SPI_DEFINES_SVH
