/*===========================================================================

Copyright © 2004, 2005 Synopsys, Inc. All rights reserved. 

This SystemVerilog Assertion Example and the associated documentation
are confidential and proprietary to Synopsys, Inc. Your use or
disclosure of this SystemVerilog Assertion Checker is subject to the
terms and conditions of a written license agreement between you, or
your company, and Synopsys, Inc.

===========================================================================*/

interface sva_std_edge_select( clk, sva_checker_clk);

  parameter   severity_level = 1;
  parameter   edge_expr      = 0;
  input       clk;
  output      sva_checker_clk;
  
  
  wire        clk;
  wire         sva_checker_clk;

  generate
    if( edge_expr == 0) begin // posedge
      assign sva_checker_clk = clk;
    end
    if( edge_expr == 1) begin // negedge
      assign sva_checker_clk = ~clk;
    end
`ifndef SYNTHESIS
    if((edge_expr >= 2) || (edge_expr < 0)) begin 
      initial begin
        sva_checker_error("Illegal clock edge_expr parameter");
//        if (severity_level == 0) $finish;
      end
    end
`endif
  endgenerate

endinterface

