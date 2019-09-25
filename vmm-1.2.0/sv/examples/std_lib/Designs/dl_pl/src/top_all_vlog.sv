/*===========================================================================

Copyright © 2004, 2005 Synopsys, Inc. All rights reserved. 

This SystemVerilog Assertion Example and the associated documentation
are confidential and proprietary to Synopsys, Inc. Your use or
disclosure of this SystemVerilog Assertion Checker is subject to the
terms and conditions of a written license agreement between you, or
your company, and Synopsys, Inc.

===========================================================================*/

module top;
   wire reset, clk, req, ack;
   wire [7:0] data;

   clk_gen clk_gen_inst(reset, clk);

   DL_PL_DUT DL_PL_DUT_inst(reset, clk, req, ack, data);

   DL_PL_MDUT DL_PL_MDUT_inst(reset, clk, req, ack, data);

   DL_PL_checker Hier_DL_PL_checker_inst(reset, clk, req, ack, data);

endmodule : top
