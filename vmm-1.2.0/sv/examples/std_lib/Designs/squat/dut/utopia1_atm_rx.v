//
//      Copyright (c) 2000 by Qualis Design Corporation.
//	All rights reserved.
//      
//	
//
//      Qualis Design Corporation
//      http://www.qualis.com
//
// Description:
//      Bus-functional model for an ATM-layer
//      Utopia level 1 receiver with cell-level flow control
//
// Author:      $Author: janick $
// Revision:    $Revision: 1.2 $
//


module utopia1_atm_rx(clk, data, soc, en, clav);

   output       clk;
   input [7:0]  data;
   input        soc; 
   output       en;  
   input        clav;

   reg          en;  

//
// Rx cell buffer.
//
// Full when cell_bfr[0] !== 1'bx
//
   reg [53*8-1:0] cell_bfr;

//
// Reset this bus-functional model
//
   reg          hold_reset;

task reset;
   input hold;
begin
   hold_reset = hold;

   cell_bfr[0] = 1'bx;
   disable listen;
end
endtask
initial reset(0);


//
// Free-running 25MHz Rx clk
//
reg  clk;
always
begin
   clk = 1'b0;
   #20; // ns
   clk = 1'b1;
   #20; // ns
end


//
// Listen to the interface, collecting byte.
// A complete cell is then copied to the cell buffer
//
always
begin: listen
   integer      i;
   reg [53*8:1] cell;

   // Reset the output signals
   en = 1'b1;

   // Wait for reset to go away
   wait (hold_reset !== 1'b1);

   // Signal we are ready to receive
   @ (posedge clk);
   en <= #1 1'b0;
   
   forever begin

      // Wait for the start of the next cell
      @ (posedge clk);
      while (soc !== 1'b1 || clav !== 1'b1) @ (posedge clk);
      
      // We have the first word.
      i = 1;
      cell = data;
      
      // Now sample the next 52 consecutive bytes
      repeat (52) begin
         cell = cell << 8;
         @ (posedge clk);
         i = i + 1;
         cell[8:1] = data;
         
         // During byte #52 (in sequence 1-53)
         // check if there will be room in the buffer.
         // If not, deassert enable during byte 53
         if (i == 52 && cell_bfr[0] !== 1'bx) begin
            en <= #1 1'b1;
         end
      end

      // Wait for the cell buffer to be empty
      wait (cell_bfr[0] === 1'bx);
      // Transfer new cell in cell buffer
      cell_bfr = cell;
      // We can receive again
      en <= #1 1'b0;
   end
end

endmodule
