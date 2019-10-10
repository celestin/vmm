/*******************************************************************************
 *
 * File:        $RCSfile: mem.v,v $
 * Revision:    $Revision: 1.5 $  
 * Date:        $Date: 2006/06/05 14:56:40 $
 *
 *******************************************************************************
 *
 *  Top-level module for the memory-mapped register in a dut
 *
 *******************************************************************************
 * Copyright (c) 1991-2005 by Synopsys Inc.  ALL RIGHTS RESERVED.
 * CONFIDENTIAL AND PROPRIETARY INFORMATION OF SYNOPSYS INC.
 *******************************************************************************
 */

`define APB_DATA_WIDTH 32

module mem(apb_if.Slave apb);



//
// Memory
//
  logic [31:0] memory ['h0000:'hffff];

  task memory_read(input logic [31:0] addr, inout logic [31:0] data);
      data = memory[addr];
  endtask 
   
   
   
//
// Hardware reset
//
always
begin: do_reset
   integer i;
   
   wait (apb.Rst === 1'b0);
   // Reset the register file
   for (i = 'h00; i <= 'hffff; i = i + 1) begin
      memory[i] = i;
   end
   // Disable all blocks
   disable mgmt_if;

   wait (apb.Rst !== 1'b0);
end


//
// Management interface
//

   // Output driver - must be 4-state for Z-drive
   logic [`APB_DATA_WIDTH-1:0] Data_out;
   assign apb.PRData = Data_out;

   always
     begin: mgmt_if
	Data_out = 'z;
	
	// Wait for reset to go away
	wait (apb.Rst === 1'b1);

	// Normal operation
	forever begin
	   
	   @ (posedge apb.PClk)
	     if(apb.PSel === 1'b1) begin
		if (apb.PWrite === 1'b1) begin
		   // PWriteite cycle
		   if(apb.PEnable === 1'b0)
		      @(posedge apb.PEnable)
		   memory[apb.PAddr % 32'h0000_ffff] = apb.PWData;
		end
		else begin
		   // Read cycle
		   if(apb.PEnable === 1'b0)
		     @(posedge apb.PEnable);
		   Data_out <= memory[apb.PAddr % 32'h0000_ffff];
		end
	     end
	end
     end
endmodule
