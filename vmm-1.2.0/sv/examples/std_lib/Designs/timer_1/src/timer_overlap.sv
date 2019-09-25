/*===========================================================================

Copyright © 2004, 2005 Synopsys, Inc. All rights reserved. 

This SystemVerilog Assertion Example and the associated documentation
are confidential and proprietary to Synopsys, Inc. Your use or
disclosure of this SystemVerilog Assertion Checker is subject to the
terms and conditions of a written license agreement between you, or
your company, and Synopsys, Inc.

===========================================================================*/

module timer;

  localparam     n       = 12;

  bit            clk     = 0;
  bit            reset   = 1;
  logic  [3:0]   cnt     = 0;
  logic  [3:0]   pre_cnt = 0;

  wire           start = cnt[0] && !pre_cnt[0];
  wire           stop  = !cnt[0] && pre_cnt[0];

  initial begin : init
    $vcdpluson;
    #20 reset = 0;
    #2000 $finish;
  end : init

  always #10 clk = !clk;

  always @(posedge clk) begin : update_cnt
    if (({$random} % 4) == 0) cnt <= cnt + 1;
    pre_cnt <= cnt;
  end : update_cnt

// ------------------------

// Example 3-22 Overlapping transactions with large time interval
  property overlap_p;
    logic [10:0] timer;
    @(posedge clk) 
      (start, timer = n) |-> 
        (timer > 0, timer=timer-1)[*0:$] ##1  stop;
  endproperty : overlap_p

  timer_overlap:  assert property (overlap_p)
    else $display("Hold time too long");

// -----------------

// Example 3-23 Property with negated boolean in the consequent

  wire a = cnt[0];
  wire b = cnt[1];

  a1: assert property (@(posedge clk) a |-> ##1 !b ) 
        else $display("After a, !b in next cycle fails");

// Example 3-24 Complemented property containing an implication.

  a2: assert property(@(posedge clk) not( a |-> ##1 b )) // Unintended ?
        else  $display("not (After a, b is true in next cycle) failed");

// Example 3-25 Moving negation to the consequent.

  a3: assert property(@(posedge clk) a |-> not( ##1 b ))  // Intended ?
        else $display("After a, not (b is true in next cycle) failed");

// ------------------

// Example 3-35 Notifier in failure action statement

  event p5_covered;

  always @p5_covered $display("Cover c5 matched at time %0d", $time);

  property p5;
    @(posedge clk) !reset throughout ($rose(cnt == 1) ##[1:$] (cnt == 10));
  endproperty : p5

  c5: cover property(p5)
    begin
       -> p5_covered;
    end

// Example 3-36 Covergroup sampling from action statement of cover property
  property p6;
    @(posedge clk) 
      !reset throughout ($rose(cnt[2]) ##[1:$] !(cnt[2]&&cnt[1]));
  endproperty : p6

  covergroup cg;
    coverpoint pre_cnt { // pre_cnt to get the same value as matched by c6
      bins which_cnt[] = {[0:15]}; }
  endgroup : cg
  cg covergroup_instance = new();

  // There shall be as many matches of c6 as the sum of all 
  // bin counts in covergroup_instance
  // alll values covered must have cnt[2] == 0 or cnt[1] == 0
  c6: cover property(p6) 
        covergroup_instance.sample();

endmodule : timer

