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

