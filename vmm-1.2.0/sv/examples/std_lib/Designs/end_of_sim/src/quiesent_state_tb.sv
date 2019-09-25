/*===========================================================================

Copyright © 2004, 2005 Synopsys, Inc. All rights reserved. 

This SystemVerilog Assertion Example and the associated documentation
are confidential and proprietary to Synopsys, Inc. Your use or
disclosure of this SystemVerilog Assertion Checker is subject to the
terms and conditions of a written license agreement between you, or
your company, and Synopsys, Inc.

===========================================================================*/

/*Coverage information for this testcase

INSTANCE NAME : SVA_QS
WIDTH = 3 
Level 1 :
cover_quiescent_state : 2/25

*/
`timescale 1ns/1ns
`define PASS 0
`define FAIL 1 

module quiesent_state_tb;

       parameter              CLK_FREQ             = 10; 		
       parameter              width                = 3;

       reg                  clk;
       reg                  reset_n;
       reg [(width - 1):0]  state_expr;
       reg [(width - 1):0]  check_value;
       reg                  sample_event;

`define ASSERT_END_OF_SIMULATION  !reset_n

task state_tran(input [width-1 :0] next_state, 
                input int condition, tdiff, tdiff_change);
  fork
    begin
      @(posedge clk);
      check_value <= (condition == `PASS) ? next_state : next_state + 3;
      if (tdiff_change > 0 )
        repeat (tdiff_change) @(posedge clk);
      state_expr  <= next_state; 
    end
    begin
      repeat(tdiff+1)@(posedge clk);
      sample_event <= 1'b1;
      @(posedge clk);
      sample_event <= 1'b0;
    end
  join
endtask : state_tran

always
  #CLK_FREQ  clk = ~clk;

initial begin
  $vcdpluson;
  clk = 1'b0;
  reset_n = 1'b0;
  state_expr = 0;
  check_value = 0;
  sample_event = 0;
  #12 reset_n = 1'b1;
end

initial begin
  #40
  state_tran(3'b011,`PASS,0,0);
  state_tran(3'b110,`PASS,2,1);
  state_tran(3'b111,`PASS,3,4);//actually a failure

  #60
  state_tran(3'b010,`FAIL,0,0);
  state_tran(3'b101,`FAIL,2,2);
  @ (posedge clk);
  sample_event <= 1'b1;
  @ (posedge clk);
  state_expr <= 3'b001;
  check_value <= 3'b001;
  #40 reset_n = 0; 
  #60 $finish;
end

assert_quiescent_state #(.width(width),.coverage_level_1(1)) 
     SVA_QS (clk, reset_n, state_expr, check_value, sample_event);

endmodule

