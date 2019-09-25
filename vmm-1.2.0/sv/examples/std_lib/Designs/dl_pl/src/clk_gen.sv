/*===========================================================================

Copyright © 2004, 2005 Synopsys, Inc. All rights reserved. 

This SystemVerilog Assertion Example and the associated documentation
are confidential and proprietary to Synopsys, Inc. Your use or
disclosure of this SystemVerilog Assertion Checker is subject to the
terms and conditions of a written license agreement between you, or
your company, and Synopsys, Inc.

===========================================================================*/

module clk_gen (reset, clk);
   output reset, clk;
   reg 	  reset, clk;

   initial begin
      $vcdpluson;
      reset = 1;
      clk = 0;
      @(posedge clk);
      @(negedge clk);
      reset = 0;
      #1000 $finish;
   end

   always #5 clk = !clk;
endmodule // clk_gen



   