/*===========================================================================

Copyright © 2004, 2005 Synopsys, Inc. All rights reserved. 

This SystemVerilog Assertion Example and the associated documentation
are confidential and proprietary to Synopsys, Inc. Your use or
disclosure of this SystemVerilog Assertion Checker is subject to the
terms and conditions of a written license agreement between you, or
your company, and Synopsys, Inc.

===========================================================================*/

/* Coverage info about this testcase :
   ASSERT_NC
   level1 : cover_driver_enable for driver[0] : 3/6
            cover_driver_enable for driver[1] : 0/6
            cover_driver_enable for driver[2] : 1/6
   level2 : obeserved_quiet_cycles : 0
   level3 : cover_no_contention_quiet_time_equal_to_max_quiet : 0/6
            cover_no_contention_quiet_time_equal_to_min_quiet : 0/6

*/

module test_no_contention;

  parameter max_quiet = 5;
  parameter min_quiet = 3;
  parameter bw_en = 3;
  parameter bw_bus = 32;

  reg [31:0] driver0 = 32'h00ff00ff;
  reg [31:0] driver1 = 32'hff00ff00;
  reg [31:0] driver2 = 32'h0f0f0f0f;

  wire [31:0] bus1;

  reg reset_n;
  reg clk;
  reg [2:0] en_vector;

  no_contention NC0 ( clk, reset_n, en_vector[0], driver0, bus1);
  no_contention NC1 ( clk, reset_n, en_vector[1], driver1, bus1);
  no_contention NC2 ( clk, reset_n, en_vector[2], driver2, bus1);

  assert_no_contention # ( 0 ,min_quiet, max_quiet, bw_en, bw_bus, 0, 
                           "failed",0,15,15,15)
         ASSERT_NC( clk, reset_n, en_vector, bus1); 

  initial begin
    $vcdpluson;
    reset_n = 1'b0;
    clk = 0;
    en_vector = 3'b0;
    repeat (2) @ ( posedge clk);
    reset_n <= 1'b1;
    en_vector <= 3'b001;
    repeat (2) @ ( posedge clk);
    repeat (1) @ ( posedge clk);
    $display("Do not expect failure on assert_no_contention_quiet_time at time %d",
             $time);
    en_vector <= 3'b100;
    repeat (1) @ ( posedge clk);
    en_vector <= 3'b010;
    @ ( posedge clk);
    en_vector <= 3'b000;
    repeat (4) @ ( posedge clk);
    en_vector <= 3'b001;
    repeat (2) @ ( posedge clk);
    $finish;
  end

  always #5 clk = ~clk;

endmodule

module no_contention( clk, reset_n, en, driver_x, bus1);
  input         clk;
  input         reset_n;
  input         en;
  input  [31:0] driver_x;
  output [31:0] bus1;

  reg  [31:0] bus1;

  always @ ( posedge clk) begin
    bus1 <= !reset_n ? 32'bz : ( en ? driver_x : 32'bz); 
  end

endmodule

