/*===========================================================================

Copyright © 2004, 2005 Synopsys, Inc. All rights reserved. 

This SystemVerilog Assertion Example and the associated documentation
are confidential and proprietary to Synopsys, Inc. Your use or
disclosure of this SystemVerilog Assertion Checker is subject to the
terms and conditions of a written license agreement between you, or
your company, and Synopsys, Inc.

===========================================================================*/

module timer;

  localparam true = 1'b1;
  typedef logic [10:0] data_t;

  bit            clk     = 0;
  bit            reset   = 1;
  data_t         cnt     = 0;
  data_t         pre_cnt = 0;

  wire           start = (cnt[7:0] == 1) && (pre_cnt[7:0] == 0);
  wire           stop  = (cnt[8:0] == 190);

  initial begin : init
    $vcdpluson;
    #20 reset = 0;
    #20000 $finish;
  end : init

  always #10 clk = !clk;

  always @(posedge clk) begin : update_cnt
    if ({$random} % 4) cnt <= cnt + 1;
    pre_cnt <= cnt;
  end : update_cnt

// ------------------------

// Example 3-20 Non-overlapping transactions with large time interval
  logic [10:0] timer = 0;

  clocking ck @(posedge clk);
    input start, stop;
  endclocking : ck

  always @(ck) begin : nooverlap
    if (reset || ck.stop)   timer <= 0;
    else if (ck.start)      timer <= 1;
    else if (timer != 0 && timer <= 255)
      timer <= timer + 1;
  end : nooverlap

  timing: assert property( 
    @(posedge clk) disable iff (reset)
      $rose(stop) || $rose(timer == 256) |-> (timer > 150) && (timer <= 255) )
  else $display("stop not within required time interval") ;

// Example 3-21 Using ternary ?: expressions
  logic [10:0] timer3 = 0;
  always @(ck) begin : nooverlap_ternary
    timer3 <= (reset || ck.stop) ? 
                0 : ck.start ? 
                     1 : (timer3 != 0 && timer3 <= 255) ?
                                     timer3 + 1 : timer3;
  end : nooverlap_ternary

  timing_3: assert property( 
    @(posedge clk) disable iff (reset)
      $rose(stop)  || $rose(timer == 256) |-> (timer3 > 150) && (timer3 <= 255) )
  else $display("stop not within required time interval") ;

// Example 3-38 Inefficient use of cover property for data coverage.
  genvar i;
  generate
    for (i=0; i<256; i++) begin : many_cov
      cnt_cov: cover property ( 
                @(posedge clk) cnt[4] && !reset && (cnt[7:0] == i[7:0]) );
    end : many_cov
  endgenerate

  // a better solution is using a covergroup
  covergroup cg @(ck);
    coverpoint cnt[7:0] iff (cnt[4] && !reset) 
      { bins cnt_cov[] = {[0:255]}; }
  endgroup
  cg cg_inst = new();

endmodule : timer

