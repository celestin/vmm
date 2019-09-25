/*===========================================================================

Copyright © 2004, 2005 Synopsys, Inc. All rights reserved. 

This SystemVerilog Assertion Example and the associated documentation
are confidential and proprietary to Synopsys, Inc. Your use or
disclosure of this SystemVerilog Assertion Checker is subject to the
terms and conditions of a written license agreement between you, or
your company, and Synopsys, Inc.

===========================================================================*/

module DL_PL_DUT(reset, clk, req, ack, data);
   input reset, clk;
   input req;
   output ack;
   output [7:0] data;

   int 	ack_latency;

   reg [7:0] 	data;
   wire		ack;
   reg [7:0] delay_line;
   integer 		 i;
   
   initial begin
      data = 0;
      delay_line = 0;
      ack_latency = {$random}%8; 
   end

   always @(posedge clk or posedge reset) begin
     if (reset) begin
       delay_line <= 0;
	   data <= 0;
     end
     else begin
       if (delay_line[ack_latency])
         ack_latency <= {$random}%7;
	   delay_line[0] <= req && !(|delay_line);
	   for (i=1; i<=ack_latency; i=i+1)
	     delay_line[i] <= delay_line[i-1];
	 
	   data <= ({$random}% 256) ^ data; // to do something on data
     end
   end // always @ (posedge clk or posedge reset)

   assign ack = delay_line[ack_latency];
   
endmodule // TL_DL_DUT


