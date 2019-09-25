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
//  Filename: wb_spi_scoreboard.sv
//  Date: 30 Oct 2009
//  Author: Doug Smith
//  Description:  Scoreboard to check the WB to SPI transfers
//
//////////////////////////////////////////////////////////////////////////////

`ifndef WB_SPI_SCOREBOARD_SV
`define WB_SPI_SCOREBOARD_SV

`include "vmm_sb.sv"

typedef vmm_sb_ds_typed#( mon_sb_trans ) sb_t;

class wb_spi_scoreboard extends sb_t;

	`vmm_tlm_analysis_export( _inp ) 
	`vmm_tlm_analysis_export( _exp )

	vmm_tlm_analysis_export_inp#( wb_spi_scoreboard, mon_sb_trans ) inp_ap = new( this, "input analysis port" );
	vmm_tlm_analysis_export_exp#( wb_spi_scoreboard, mon_sb_trans ) exp_ap = new( this, "expect analysis port" );
	

	function new( string name );
		super.new( name );
		//define_stream( 0, "SPI", INPUT ); 
		//define_stream( 1, "WB", EXPECT ); 
	endfunction

	function bit compare( mon_sb_trans actual, mon_sb_trans expected );
		bit	[127:0]	mask = '0;

		// Create a mask based on the number of bits transmitted
		for (int i = 0; i < (expected.ctrl & 'h3f); i++)
			mask[i] = 1;
		
		`vmm_note( this.log, "Checking data..." );

		// Only need to compare the data
		return ((actual.data & mask) == (expected.data & mask));
	endfunction

	// Provide an implementation for the TLM analysis ports
	function void write_inp(int id=-1, mon_sb_trans trans);
		// Actual value so check to see if it's correct
		void'(this.expect_in_order( trans, id ));
	endfunction
	
	function void write_exp(int id=-1, mon_sb_trans trans);
		// Expect this transaction
		this.exp_insert( trans, id );
	endfunction

endclass : wb_spi_scoreboard


`endif	// WB_SPI_SCOREBOARD_SV
