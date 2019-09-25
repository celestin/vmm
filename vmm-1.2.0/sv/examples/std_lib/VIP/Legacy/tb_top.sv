//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

// Example 4-96
module tb_top;

wire [11:0] Addr_0;
wire [ 7:0] Data_0;
wire        Sel_0;
wire        Rd_DS_0;
wire        Wr_RW_0;
wire        Rdy_0;

wire [11:0] Addr_1;
wire [ 7:0] Data_1;
wire        Sel_1;
wire        Rd_DS_1;
wire        Wr_RW_1;
wire        Rdy_1;

utopia_mgmt_bfm host0(Addr_0, Data_0, Sel_0,
                      Rd_DS_0, Wr_RW_0, Rdy_0);

utopia_mgmt_bfm host1(Addr_1, Data_1, Sel_1,
                      Rd_DS_1, Wr_RW_1, Rdy_1);

endmodule
