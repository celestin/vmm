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
module test_top;
  parameter simulation_cycle = 100;

  reg  SystemClock;

  wire 		clk;
  logic 	reset;
  wire 		busRdWr_N;
  wire 		adxStrb;
  wire [7:0]	busAddr;
  wire [1:0]	request;
  wire [1:0]	grant;
  wire [7:0]	busData;
  assign clk = SystemClock;

  cpu_if port0(clk, busRdWr_N, adxStrb, busAddr, request[0], busData, grant[0]);
  cpu_if port1(clk, busRdWr_N, adxStrb, busAddr, request[1], busData, grant[1]);
   

  memsys_tb tb();

  memsys dut(
    .clk	(clk),
    .reset	(reset),
    .busRdWr_N	(busRdWr_N),
    .adxStrb	(adxStrb),
    .busAddr	(busAddr),
    .request	(request),
    .busData	(busData),
    .grant	(grant)
  );


  initial begin
    SystemClock = 0;
    forever begin
      #(simulation_cycle/2)
        SystemClock = ~SystemClock;
    end
  end

  initial $vcdpluson;
endmodule
