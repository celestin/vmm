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
//  Filename: wb_spi_trans.sv
//  Date: 30 Oct 2009
//  Author: Doug Smith
//  Description:  Transaction class/data type for the SPI driver.
//
//////////////////////////////////////////////////////////////////////////////


`ifndef WB_SPI_TRANS_SV
`define WB_SPI_TRANS_SV

class wb_spi_trans extends vmm_data;

   // Fields in the SPI registers
   rand bit [AWIDTH-1:0] addr;
   rand bit [DWIDTH-1:0] data;
   rand trans_t          kind;

   `vmm_typename( wb_spi_trans )

   // Create the constructor, copy(), and allocate() functions
   `vmm_data_member_begin( wb_spi_trans )
	`vmm_data_member_scalar( addr,    DO_ALL )
	`vmm_data_member_scalar( data,    DO_ALL )
	`vmm_data_member_enum  ( kind,    DO_ALL )
   `vmm_data_member_end( wb_spi_trans )

   // Create a class factory so this transaction can be swapped with derived
   // classes.
   `vmm_class_factory( wb_spi_trans )

endclass : wb_spi_trans

// Create the channel class for the wb_spi_trans
`vmm_channel ( wb_spi_trans )

`endif	// WB_SPI_TRANS_SV
