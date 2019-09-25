/*===========================================================================

Copyright © 2004, 2005 Synopsys, Inc. All rights reserved. 

This SystemVerilog Assertion Example and the associated documentation
are confidential and proprietary to Synopsys, Inc. Your use or
disclosure of this SystemVerilog Assertion Checker is subject to the
terms and conditions of a written license agreement between you, or
your company, and Synopsys, Inc.

===========================================================================*/

// model generating waveforms conforming to Figure 7-3.

module figure7_3(input bit clk, reset, logic a, b, d, output logic c);
  logic w = 0;
  logic [4:0] cnt = 0;

  always @(posedge clk) 
    if (reset) cnt = 0; else cnt <= (cnt<<1) | {4'b0, (cnt[4]^b)};

  always @(posedge clk) 
    if (reset) w <= 0; 
    else if (a) w <= 1; else if (d) w <= 0;

  always @(cnt[4] or w or d)
    c = w && cnt[4] &&!d;

`ifndef NO_INLINED_ASSERTION

// Example 7-17 Unbounded branching with variable assignment
  property p1;
    bit [7:0] x;
    @(posedge clk)
      (a, x = 0) ##1 (!c[*0:$]) ##1
      ( ((c, x = x+1) ##1 (!c[*0:$]))[*0:$] ) ##1 d
        |->
          (x <= 8'd10);
  endproperty : p1

  a7_17: assert property (p1);


// Example 7-18 One copy of x for each attempt
  property p2;
    bit [7:0] x;
    @(posedge clk)
      (a, x = 0) ##1 
      (
        !d throughout 
            (!c[*0:$]) ##1
            ( ((c, x = x+1) ##1 (!c[*0:$]))[*0:$] )
      ) 
      ##1 d
        |-> (x <= 8'd10);
  endproperty : p2

  a7_18: assert property (p2);

// Example 7-19 Using if-else and recursion
/* Not implemented yet
  property p3;
    int x;
    @(clk) (a, x = 0) |=> p_rec(x);
  endproperty : p3
  property p_rec(x);
    @(clk)
    if (d) 
      (x <= 8'd10)
    else 
      if (c) (1, x=x+1) |=> p_rec(x)
      else   1 |=> p_rec(x) ;
  endproperty : p_rec

  a7_19: assert property (p3);
*/ 

// Example 7-20 Using repetition, vacuous success on an additional a
  property p4;
    int x;
    @(clk)
      (a, x = 0) ##1 
      (
        !d && !a throughout 
           (!c[*0:$]) ##1
           ( ((c, x = x+1) ##1 (!c[*0:$]))[*0:$] )
      ) 
      ##1 d
           |-> (x <= 8'd10);
  endproperty : p4

  a7_20: assert property (p4);


// Example 7-21 Signalling failure if another a before and including d
  a7_21: assert property // check no extra a
    (@(posedge clk)
      (a |=> !a throughout (d[->1]) ) 
    );

// Example 7-22 Using a static counter to count c's.
  localparam MAX_C = 8'd11; // value > exp
  logic [7:0] x = MAX_C; 
  always @(posedge clk) x <= d || a?
                               0 : 
                                 c && (x<MAX_C) ?
                                      x+1 :
                                      x ;
  property p5; 
    @(posedge clk) 
      d || c |-> (x < 8'd10);
  endproperty : p5
  // The assertion will fail on any c that exceeds the maximum of 8'd10.
  // This is unlike the other assertions where a failure is detected 
  // only when d occurs and the count of c's exceeds the maximum. 
  // It is left to the reader to modify this assertion or the others so that 
  // all have the same reporting - either all when d occurs or whenever c 
  // occurs that exceeds the maximum count.
  a7_22: assert property (p5);

`endif

endmodule : figure7_3


module figure7_3_tb;
  bit clk=0, reset=1;
  logic a = 0, b = 0, d = 0, v = 0;
  wire c;

  initial begin
    $vcdpluson;
    #10 reset = 0;
    #3000 $finish;
  end

  always #5 clk = !clk;

  always @(posedge clk) begin
    a <= (({$random} % 8) == 0) && !a && !v;
    if (a) v <= 1; else if (d) v <= 0;
    if (v) begin
      d <= (({$random} % 16) == 0);
      b <= (({$random} % 2) == 0);
    end 
    else begin
      d <= 0;
      b <= 0;
    end
  end

  figure7_3 figure7_3_inst(.*);

endmodule : figure7_3_tb
