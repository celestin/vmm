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
//      Utopia level 1 transmitter with cell-level flow control
//
// Author:      $Author: janick $
// Revision:    $Revision: 1.2 $
//

module utopia1_atm_tx(clk, data, soc, en, clav);

output       clk;
output [7:0] data;
output       soc; 
output       en;  
input        clav;

reg [7:0] data;
reg       en;
reg       soc;

//
// Tx cell buffer.
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
   disable talk;
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
// Talk to the interface, sending
// cells from the Tx buffer
//
always
begin: talk
   integer      i;
   reg [53*8:1] cell;

   // Reset the output signals
   data = 8'hXX;
   soc  = 1'b0;
   en   = 1'b1;

   // Wait for reset to go away
   wait (hold_reset !== 1'b1);

   // Synchronize with the clock
   @ (posedge clk);

   forever begin
      
      // First, wait for a cell in the Tx buffer
      while (cell_bfr[0] === 1'bx) begin
         en <= #1 1'b1;
         @ (posedge clk);
      end

      // Grab the cell out of the Tx buffer
      cell = cell_bfr;
      cell_bfr[0] = 1'bx;

      // Wait for the PHY layer to indicate it
      // can accept a cell
      while (clav !== 1'b1) begin
         en <= #1 1'b1;
         @ (posedge clk);
      end
   
      // Indicate the start of the next cell
      soc  <= #1 1'b1;
      data <= #1 cell[424:417];
      en   <= #1 1'b0;
      i     = 1;
      @ (posedge clk);

      // Now send the next 52 consecutive bytes
      repeat (52) begin
         cell = cell << 8;
         soc  <= #1 1'b0;
         data <= #1 cell[424:417];
         en   <= #1 1'b0;
         i     = i + 1;
         @ (posedge clk);
      end
   end
end

endmodule

