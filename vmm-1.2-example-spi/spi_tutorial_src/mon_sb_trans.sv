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
//  Filename: mon_sb_trans.sv
//  Date: Feb 2010
//  Author: Doug Smith
//  Description:  Transaction class/data type for the monitors and scoreboard.
//
//////////////////////////////////////////////////////////////////////////////


`ifndef MON_SB_TRANS_SV
`define MON_SB_TRANS_SV

class mon_sb_trans extends vmm_data;

   // Fields in the SPI registers
   rand bit [AWIDTH-1:0]     addr;
   rand bit [(DWIDTH*4)-1:0] data;
   rand trans_t              kind;
   rand ctrl_t               ctrl;

   `vmm_typename( mon_sb_trans )

   // Define function coverage
   covergroup cg;
        coverpoint addr {
                bins valid[] = { SPI_TX_RX0, SPI_TX_RX1, SPI_TX_RX2,
                                SPI_TX_RX3, SPI_CTRL, SPI_DIVIDER, SPI_SS };
                illegal_bins invalid = default;
        }
        char_len: coverpoint ctrl.char_len {
                bins tiny = { [1:43] };
                bins mid  = { [44:85] };
                bins big  = { 0, [86:127] };
        }
        coverpoint kind;
   endgroup

   `vmm_data_new( mon_sb_trans )
   function new();
        super.new( log );
        cg = new;       // Create the coverage
   endfunction

   // Function to sample the coverage
   function void sample_cov();
        cg.sample();
   endfunction


   // Create the constructor, copy(), and allocate() functions
   `vmm_data_member_begin( mon_sb_trans )
        `vmm_data_member_scalar( addr,    DO_ALL )
        `vmm_data_member_scalar( data,    DO_ALL )
        `vmm_data_member_scalar( ctrl,    DO_ALL )
        `vmm_data_member_enum  ( kind,    DO_ALL )
   `vmm_data_member_end( mon_sb_trans )

endclass : mon_sb_trans

`endif	// MON_SB_TRANS_SV
