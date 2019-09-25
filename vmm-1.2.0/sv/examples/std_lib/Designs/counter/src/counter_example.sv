/*===========================================================================

Copyright © 2004, 2005 Synopsys, Inc. All rights reserved. 

This SystemVerilog Assertion Example and the associated documentation
are confidential and proprietary to Synopsys, Inc. Your use or
disclosure of this SystemVerilog Assertion Checker is subject to the
terms and conditions of a written license agreement between you, or
your company, and Synopsys, Inc.

===========================================================================*/

module counter;

  localparam true = 1'b1;

  bit            clk = 0;
  logic [4:0]    cnt = 0;

  wire y = (cnt == 0);
  wire a = cnt[0];
  wire b = (cnt == 10);
  wire c = (cnt == 16);
  wire x = cnt[4];

  initial begin : init
    $vcdpluson;
    #2000 $finish;
  end : init

  always #10 clk = !clk;

  always @(posedge clk) 
    if ({$random} % 2) cnt <= cnt + 1;

// Example 3-15 Constraining by intersection to limit length
  a_length : assert property (
    @(posedge clk) 
      y |=> 1'b1 [*20:30]
              intersect
            (a ##[1:$] b ##[1:$] c)
    ) else $display("length limit fail at %0d", $time);

// Example 3-16 Bounding length using within
  a_within : assert property (
    @(posedge clk)
      y |-> (a ##[1:$] b ##[1:$] c)
              within
             x[->2]
    ) else 
        $display("bound by within fail at %0d", $time);

  a_within_once : assert property (
    @(posedge clk)
      y |-> (a [->1] ##1 b[->1] ##1 c[=1])
              intersect
             x[->2]
    ) else 
        $display("bound by within only once fail at %0d", $time);

  sequence s0;
    cnt[0] ##2 cnt[1];
  endsequence : s0
  sequence s1;
    (cnt == 9) ##1 b;
  endsequence : s1
  sequence s2;
    (cnt == 10) ##1 (cnt == 11);
  endsequence : s2

// Example 3-17 Using go-to in place of ##[1:$]
  a_go_to: assert property (
    @(posedge clk)
      s0 ##1 b[->1] |=> s2
    ) else
        $display("goto match and s2 fail at %0d", $time);

// Example 3-18 Using first_match operator
  a_first_match: assert property (
    @(posedge clk)
      s0 ##1 first_match( ##[1:$] s1 ) |=> s2
    ) else
        $display("first_match and s2 fail at %0d", $time);

// Example 7-1 Breaking a property into smaller ones

  wire v = cnt[0];
  wire w = cnt[1];
  wire z = cnt[2] && cnt[0];

// If v occurs then at that time w must also be asserted 
// for one cycle and followd by z in 1 to 5 cycles.
  property p;
    @(posedge clk)
    v |-> w ##1 !w ##[0:4] z;
  endproperty : p
  a_p: assert property (p);

// The properties p1, p2 and p3 imply collectively p.
// However, if w can also occur without an v, and then have
// a different behavior than when a is present,
// a_p2 or a_p3 could fail while a_p would not.
// If a w should not occur without an v, then add the 
// property p_auxiliary and the associated assertion.
//
// In this test, a_p_auxiliary fails, but it can be seen
// that whenever a_p1, a_p2, a_p3 and a_p_auxiliary succeed, 
// a_p succeeds as well - it truths is implied by the 
// collection of small properties.
// Notice also that when a_p1 or a_p2 or a_p3 fail and a_p does not
// then also a_p_auxiliary fails, indicating that this is 
// the behavior under which the truth of the original property 
// does not imply the truth of the collection.

  property p1;
    @(posedge clk)
    v |-> w; // if v then w
  endproperty : p1
  a_p1: assert property (p1); 

  property p2;
    @(posedge clk)
    w |-> ##1 !w;
  endproperty : p2
  a_p2: assert property (p2);

  property p3;
    @(posedge clk)
    w |-> ##[1:5] z;
  endproperty : p3
  a_p3: assert property (p3);

  property p_auxiliary;
    @(posedge clk)
    w |-> v;
  endproperty : p_auxiliary
  a_p_auxiliary: assert property(p_auxiliary);

endmodule : counter