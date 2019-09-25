//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

//
// Legacy Verilog Parallel Utopia Management Interface
//
// The ATM Forum Technical Committee
// "Utopia Level 2, Version 1.0"
// af-phy-0039.000
// June 1995
// Section A2.4
//

`timescale 1ns / 1ns
module utopia_mgmt_bfm(Addr, Data, Sel, Rd_DS, Wr_RW, Rdy_Dtack);

output [11:0] Addr;
inout  [ 7:0] Data;
output        Sel;
output        Rd_DS;
output        Wr_RW;
input         Rdy_Dtack;

parameter BusMode = 1;

reg [11:0] Addr;
reg [ 7:0] Dout;
wire [7:0] Din = Data;
assign     Data = Dout;
reg        Sel;
reg        Rd_DS;
reg        Wr_RW;


initial reset;

task reset;
begin
   Sel   = 1'b1;
   Rd_DS = 1'b1;
   Wr_RW = 1'b1;      
   Dout  = 8'hZZ;
end
endtask

task read(input  [11:0] radd,
          output [ 7:0] rdat);
begin
   Addr = radd;
   #5;
   Sel   = 1'b0;
   #5;
   Rd_DS = 1'b0;
   #50;
   wait (Rdy_Dtack === 1'b0);
   rdat = Din;
   Rd_DS = 1'b1;
   Sel   = 1'b1;
   #4;
end
endtask


task write(input [11:0] wadd,
           input [ 7:0] wdat);
begin
   Addr = wadd;
   #5;
   Sel   = 1'b0;
   if (BusMode === 1'b0) Wr_RW = 1'b0;
   #5;
   if (BusMode === 1'b1) Wr_RW = 1'b0;
   else                  Rd_DS = 1'b0;
   fork
      begin
         #15;
         @ (negedge Rdy_Dtack);
         Dout = wdat;
         #15;
      end
      #50;
   join
   if (BusMode === 1'b1) Wr_RW = 1'b1;
   else                  Rd_DS = 1'b1;
   Sel   = 1'b1;
   #4;
   Dout = 8'hZZ;
end
endtask

endmodule
