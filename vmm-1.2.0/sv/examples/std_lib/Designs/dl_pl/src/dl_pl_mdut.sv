/*===========================================================================

Copyright © 2004, 2005 Synopsys, Inc. All rights reserved. 

This SystemVerilog Assertion Example and the associated documentation
are confidential and proprietary to Synopsys, Inc. Your use or
disclosure of this SystemVerilog Assertion Checker is subject to the
terms and conditions of a written license agreement between you, or
your company, and Synopsys, Inc.

===========================================================================*/

module DL_PL_MDUT(reset, clk, req, ack, data);
   input reset, clk, ack;
   input [7:0] data;
   
   output req;
   reg	  req;

   reg [9:0] delay;
   int   i;
   int req_latency = 4;
   
   initial begin
      delay = 8'b1;
   end

   always @(posedge clk or posedge reset) begin
     if (reset) begin
       delay <= 8'b1;
	   req <= 0;
     end
     else begin
	   delay <= {8'b0,ack};
	   for (i=1; i<10; i = i+1)
	     delay[i] <= delay[i-1];
       if (ack) begin
         req <=  0 ;
         req_latency <= {$random}%8;
       end 
       else 
         req <= delay[req_latency] && !req ? 1'b1 : req;
     end // else: !if(reset)
   end // always @ (posedge clk or posedge reset)

endmodule // req_gen
