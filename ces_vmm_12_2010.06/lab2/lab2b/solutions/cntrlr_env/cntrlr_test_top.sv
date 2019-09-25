
`include "cpu_if.sv"
`include "sram_if.sv"

module test_top;
  parameter RAM_ADDR_WDTH = 8;
  parameter NUM_OF_SRAMS = 4;
  parameter simulation_cycle = 100;

  logic SystemClock;
  logic reset;

  cpu_if cpuif (SystemClock);
  sram_if sramif0(SystemClock, dut.ce0_N, dut.rdWr_N, dut.ramAddr, dut.ramData);
  sram_if sramif1(SystemClock, dut.ce1_N, dut.rdWr_N, dut.ramAddr, dut.ramData);
  sram_if sramif2(SystemClock, dut.ce2_N, dut.rdWr_N, dut.ramAddr, dut.ramData);
  sram_if sramif3(SystemClock, dut.ce3_N, dut.rdWr_N, dut.ramAddr, dut.ramData);
   
  cntrlr_tb tb();

  cntrlr#(RAM_ADDR_WDTH, NUM_OF_SRAMS) dut(.clk(SystemClock), 
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
