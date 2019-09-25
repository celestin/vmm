
`include "cpu_if.sv"

module test_top;
  parameter RAM_ADDR_WDTH = 6;
  parameter NUM_OF_SRAMS = 4;
  parameter simulation_cycle = 100;

  reg  SystemClock;
             
  wire         clk;
  logic        reset;
  assign clk = SystemClock;

  cpu_if cpuif (clk);
   
  cntrlr_tb tb();

  cntrlr#(RAM_ADDR_WDTH, NUM_OF_SRAMS) dut(.clk(clk), 
                                           .reset(reset), 
                                           .busAddr(cpuif.busAddr), 
                                           .busData(cpuif.busData), 
                                           .busRdWr_N(cpuif.busRdWr_N), 
                                           .adxStrb(cpuif.adxStrb));

//-----------------------------------------------------------------------------
// Clock generation logic.
//-----------------------------------------------------------------------------

  initial begin
    SystemClock = 0;
    forever begin
      #(simulation_cycle/2)
        SystemClock = ~SystemClock;
    end
  end

  initial $vcdpluson;
endmodule
