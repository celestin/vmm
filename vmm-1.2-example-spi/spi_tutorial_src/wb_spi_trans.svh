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
//  Filename: wb_spi_trans.svh
//  Date: 30 Oct 2009
//  Author: Doug Smith
//  Description:  Contains types for the transaction class.
//
//////////////////////////////////////////////////////////////////////////////

`ifndef WB_SPI_TRANS_SVH
`define WB_SPI_TRANS_SVH

typedef enum { RX, TX } trans_t;
typedef struct packed {
	bit [31:14]	reserved1;
   	bit		a_ss;
   	bit		ie;
   	bit		lsb;
   	bit		tx_neg;
   	bit		rx_neg;
   	bit		go_bsy;
   	bit		reserved2;
   	bit [6:0]	char_len;
} ctrl_t;

typedef struct packed {
   	bit [31:16]	reserved;
   	bit [15:0]	freq_div;
} divider_t;

typedef struct packed {
   	bit [31:8]	reserved;
   	bit [7:0]	slave_select;
} ss_t;

`endif		// WB_SPI_TRANS_SVH
