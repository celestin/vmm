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






`include "cpu_if.sv"
`include "sram_if.sv"

module test_top;
  parameter RAM_ADDR_WDTH = 6;
  parameter NUM_OF_SRAMS = 4;
  parameter simulation_cycle = 100;

  reg  SystemClock;
             
  wire         clk;
  logic        reset;
  assign clk = SystemClock;

  cpu_if cpuif (clk);
  sram_if sramif0(clk, dut.ce0_N, dut.rdWr_N, dut.ramAddr, dut.ramData);
  sram_if sramif1(clk, dut.ce1_N, dut.rdWr_N, dut.ramAddr, dut.ramData);
  sram_if sramif2(clk, dut.ce2_N, dut.rdWr_N, dut.ramAddr, dut.ramData);
  sram_if sramif3(clk, dut.ce3_N, dut.rdWr_N, dut.ramAddr, dut.ramData);
   
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
