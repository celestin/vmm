interface cpu_if (input bit clk);
  wire	        busRdWr_N;
  wire	        adxStrb;
  wire [31:0]   busAddr;
  wire [ 7:0]   busData;
  wire          cpu_req;
  wire 		cpu_grant;

  clocking cb @(posedge clk);
    output busAddr;
    inout  busData;
    output adxStrb;
    output busRdWr_N;
  endclocking

  modport drvprt(clocking cb);
endinterface

