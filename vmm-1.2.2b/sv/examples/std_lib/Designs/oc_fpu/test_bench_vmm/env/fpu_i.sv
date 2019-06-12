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

interface fpu_i(input logic clk);
    wire [1:0]	    rmode;
    wire [2:0]	    fpu_op;
    wire [31:0]    opa;
    wire [31:0]    opb;
    wire [31:0]    out;
    wire	    inf;
    wire	    snan;
    wire	    qnan;
    wire	    ine ;
    wire	    overflow;
    wire	    underflow;
    wire	    zero     ;
    wire	    div_by_zero;
   
    //Clocking block for testbench synchronous code
    clocking cb @(posedge clk);
	output rmode, 
               fpu_op, 
               opa, 
               opb;
        input  out, 
               inf,
	       snan,
	       qnan,
	       ine ,
	       overflow,
	       underflow,
	       zero,
	       div_by_zero;
    endclocking

    //Modport for Sync. testbench accesses
    modport STB(clocking cb);

    //modport for any asynchronous accesses if required from tb
    modport ASTB(
	output rmode, 
               fpu_op, 
               opa, 
               opb,
        input  out, 
               inf,
	       snan,
	       qnan,
	       ine ,
	       overflow,
	       underflow,
	       zero,
	       div_by_zero
        );

    //modport for accesses from DUT
    modport ADUT(
	input  rmode, 
               fpu_op, 
               opa, 
               opb,
        output out, 
               inf,
	       snan,
	       qnan,
	       ine ,
	       overflow,
	       underflow,
	       zero,
	       div_by_zero
        );
    
endinterface

