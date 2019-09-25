
/******************************************************************************
*  Top-level module for the memory-mapped register in a dut
******************************************************************************/

interface host_if;
   logic [4:0] addr;
   logic       sel;
   wire  [7:0] data,
   logic       rd;
   logic       wr;
   logic       rdy;
endinterface

module dut(host_if if,
           input   rst,
           inout   clk);

//
// Register file
//
   reg [7:0]   regfile ['h00:'h1f];

//
// Hardware reset
//
always
begin: do_reset
   integer i;
   
   wait (rst === 1'b0);
   // Reset the register file
   for (i = 'h00; i <= 'h1f; i = i + 1) begin
      regfile[i] = '0;
   end
   // Disable all blocks
   disable mgmt_if;

   wait (rst !== '0);
end


//
// Management interface
//

   // AC timing characteristics
   parameter t4 = 10;
   parameter t6 = 05;
   parameter t7 = 10;
   parameter t9 = 15;
   parameter delay = 20;

   // Output drivers
   reg [7:0] dout;
   assign    if.data = dout;

always
begin: mgmt_if
   dout   = 'z;
   if.rdy = '0;
   
   // Wait for reset to go away
   wait (rst === '1);

   // Normal operation
   forever begin: do_cycle
      
      @ (negedge if.rd or negedge if.wr);
      #(t6);
      if.rdy <= '1;
      #(delay);
      if.rdy <= '0;
      if (if.wr === '0) begin
         // Write cycle
         @ (posedge if.wr);
         // Addresses 0-7 is read-only
         if (if.addr > 5'h07) regfile[if.addr] = if.data;
      end
      else begin
         // Read cycle
         dout <= #(t4) regfile[if.addr];
         @ (posedge if.rd);
         dout <= #(t9) 'z;
      end
      if.rdy <= #(t7) '0;
   end
end
endmodule
