//
// -------------------------------------------------------------
//    Copyright 2004-2009 Synopsys, Inc.
//    All Rights Reserved Worldwide
//
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//

`timescale 1ns / 100ps 
module top;
    reg             clk       ; 
    wire [1:0]	    rmode     ; 
    wire [2:0]	    fpu_op    ; 
    wire [31:0]	    opa       ; 
    wire [31:0]	    opb       ; 
    wire [31:0]     out       ; 
    wire		    inf       ; 
    wire		    snan      ; 
    wire		    qnan      ; 
    wire		    ine       ; 
    wire		    overflow  ; 
    wire		    underflow ; 
    wire		    zero      ; 
    wire		    div_by_zero;

  fpu_i fpu_intf(.clk(clk));

  test testb(.iport(fpu_intf));

  //ToDo:  fix the DUT to have interface as inputs.
  fpu dut(
   .clk       (clk       ),
   .rmode     (rmode     ),
   .fpu_op    (fpu_op    ),
   .opa       (opa       ),
   .opb       (opb       ),
   .out       (out       ),
   .inf       (inf       ),
   .snan      (snan      ),
   .qnan      (qnan      ),
   .ine       (ine       ),
   .overflow  (overflow  ),
   .underflow (underflow ),
   .zero      (zero      ),
   .div_by_zero(div_by_zero)  
  );

  //ToDo: fix / remove when DUT take fpu_intf as a port
//Inputs to DUT
assign rmode     = fpu_intf.rmode;
assign fpu_op    = fpu_intf.fpu_op;
assign opa       = fpu_intf.opa;
assign opb       = fpu_intf.opb;

//Outputs from DUT
assign fpu_intf.out        = out       ;
assign fpu_intf.inf        = inf       ;
assign fpu_intf.snan       = snan      ;
assign fpu_intf.qnan       = qnan      ;
assign fpu_intf.ine        = ine       ;
assign fpu_intf.overflow   = overflow  ;
assign fpu_intf.underflow  = underflow ;
assign fpu_intf.zero       = zero      ;
assign fpu_intf.div_by_zero = div_by_zero;  


`ifdef VPD
  initial 
     if ($test$plusargs("dump")) $vcdpluson;
`endif

`ifdef VCD
  initial
     if ($test$plusargs("dump")) $dumpvars;
`endif

  initial begin
     clk = 0;
     forever begin
        #50;
        clk = ~clk;
     end
  end
  
endmodule  
