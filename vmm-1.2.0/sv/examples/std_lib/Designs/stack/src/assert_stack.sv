/*===========================================================================

Copyright © 2004, 2005 Synopsys, Inc. All rights reserved. 

This SystemVerilog Assertion Example and the associated documentation
are confidential and proprietary to Synopsys, Inc. Your use or
disclosure of this SystemVerilog Assertion Checker is subject to the
terms and conditions of a written license agreement between you, or
your company, and Synopsys, Inc.

===========================================================================*/

/*

assert_stack

This unit implements checking of operations on a stack.

The size of the stack is depth, a compile-time integer constant 
< 2**16.  The width of the elements is elem_sz, a compile-time
constant.

reset_n asserted 0 initializes the stack to empty.

All operations including reset_n are synchronous the a tick of
clk.

When push is asserted 1: Ensures no stack overflow.  push_lat
specifies the number of ticks of clk between the asserting of push
and when push_data is valid. It must be a compile-time non-negative
integer constant (not an interval).

If hi_water_mark is a positive value, then the fill of the stack after
the push will be checked to see if hi_water_mark is exceeded.  Once
high water has been exceeded once, this check is disabled until the
stack falls to or below the mark again (<=). hi_water_mark can be a
constant or a design variable.

If the stack depth is exceeded a failure is reported and all further
checks are disabled until the stack is reset.

When pop is enabled: Ensures the stack was not empty when popped. If
a pop is performed on an empty stack, all checking of pop operations
is disabled until reset is applied or a push occurs.

If value_chk evaluates 1, it ensures pop_data is what was on the
top of the stack.  pop_lat specifies the number of cycles of clk
between the asserting of pop and when pop_data is valid. It must
be a compile-time non-negative integer constant (not an interval).

If push_pop_chk evaluates 1, ensures that push and pop operations do
not occur simultaneously. If push and pop do occur simultaneously, the
effect is the same as if push were done first followed by a pop (i.e.,
the stack is not changed). If value_chk = 1 then pop_data is
compared with push_data in that case.

Defaults:

depth = 2
elem_sz = 1
hi_water_mark = 0 meaning not checked
push_lat = 0 meaning at the same time as deferred push sampled 1
pop_lat = 0 meaning at the same time as deferred pop sampled 1
value_chk = 1 enabled
push_pop_chk = 1 enabled

Failure modes:

Assertion assert_stack_overflow will report a failure when push is
issued and the stack is full. The reported time of failure is on the
clock tick following the failed deferred push operation.

Assertion assert_stack_underflow will report a failure when pop is
issued and the stack is empty(and no simultaneous push). The
reported time of failure is on the clock tick following the failed
deferred push operation.

Assertion assert_stack_value_chk will report failure when pop_data
value does not match the expected top-of-stack value, provided the
stack is not empty or when the stack is empty and there is a
simultaneous push and the value pushed on the stack does not match
the value popped off the stack.

Assertion assert_stack_hi_water_chk will report a failure if the stack
is filled above the high-water mark.

Assertion assert_stack_push_pop_fail will report a failure if push
and pop are enabled simultaneously (and push_pop_chk is 1).

 
Coverage modes :

cov_level_1_0 (bit 0 set in coverage_level_1) : 

 Cover property, cover_number_of_pushes, indicates that there
 was a push operation.

cov_level_1_1 (bit 1 set in coverage_level_1) : 

 Cover property, cover_number_of_pop,s indicates that there
 was a pop operation.

cov_level_1_2 (bit 2 set in coverage_level_1) : 

 Cover property, cover_push_followed_eventually_by_pop, indicates that
 a push was followed eventually by a pop without an intervening push.

cov_level_2_0 (bit 0 set in coverage_level_2) :

 Cover point, observed_outstanding_contents, reports which observed
 fill levels were observed at least once.

cov_level_3_0 (bit 0 set in coverage_level_3) :

 Cover property, cover_stack_hi_water_chk, indicates that the
 high water mark was reached.

cov_level_3_1 (bit 1 set in coverage_level_3) :

 Cover property, cover_simultaneous_push_pop, indicates that
 there were simultaneous push and pop operations.

cov_level_3_2 (bit 2 set in coverage_level_3) :

 Cover property, cover_simultaneous_push_pop_when_empty, indicates
 that there were simultaneous push and pop operations while the
 stack was empty.

cov_level_3_3 (bit 3 set in coverage_level_3) :

 Cover property, cover_simultaneous_push_pop_when_full, indicates that
 there were simultaneous push and pop operations while the
 stack was full.

cov_level_3_4 (bit 4 set in coverage_level_3) :

 Cover property, cover_number_of_empty, indicates that the
 stack became empty after a pop.

cov_level_3_5 (bit 5 set in coverage_level_3) :

 Cover property, cover_number_of_full, indicates that the
 stack became full after a push.


Example:

assert_stack #(0, 10, 16, 8, 0, 0,  1, 0)
       stack_inst (clk, !sys_reset, 
                   push, data_in, 
                   pop, data_out);
 
When sys_reset is asserted the stack is initialized. It is 10 elements
deep and 16 bits wide. The water mark is set at 8 which means that the
water-mark check is enabled. The push and pop latencies are both 0
which means that data_in must be present at the same time as push is
asserted and data_out must be present at the same time as pop is
asserted. The value check is enabled meaning that data_out will be
checked against the data expected on the top of the stack. Push-Pop
check is disabled. Coverage Level 1 is selected by default.

*/

`undef SVA_ASSERT_AND_COVER
`ifdef ASSERT_ON
  `define SVA_ASSERT_AND_COVER
`endif
`ifndef SVA_ASSERT_AND_COVER
  `ifdef COVER_ON
     `define SVA_ASSERT_AND_COVER
  `endif
`endif

// Example 3-39 Checker packaging
(* sva_checker *)
interface assert_stack( clk, reset_n, push , push_data, pop, pop_data);

       parameter              severity_level         = 0;
       parameter              depth                  = 2;
       parameter              elem_sz                = 1;
       parameter              hi_water_mark          = 0;
       parameter              push_lat               = 0;
       parameter              pop_lat                = 1;
       parameter              value_chk              = 1;
       parameter              push_pop_chk           = 1;
       parameter              edge_expr              = 0;
       parameter              msg                    = "VIOLATION";
       parameter              category               = 0; 
       parameter              coverage_level_1       = 15; 
       parameter              coverage_level_2       = 0; 
       parameter              coverage_level_3       = 0; 
       input                  reset_n;
       input                  clk;
       input                  push;
       input [elem_sz-1:0]    push_data;
       input                  pop;
       input [elem_sz-1:0]    pop_data;
       
     `ifdef SVA_ASSERT_AND_COVER

       localparam             assert_name            = "ASSERT_FIFO";

       wire                   reset_n;
       wire                   clk;
       wire                   push;
       wire  [elem_sz-1:0]    push_data;
       wire                   pop;
       wire  [elem_sz-1:0]    pop_data;

       wire                   sva_checker_clk;

       wire                   sva_v_deferred_pop; 
       wire                   sva_v_deferred_push;

       reg      [16:0]        sva_v_stack_ptr;
       reg                    sva_v_empty_chk_failed;
       reg                    sva_v_full_chk_failed;
       reg      [16:0]        past_sva_v_stack_ptr;



`include "sva_std_task.h"

`ifndef SYNTHESIS
       initial begin
          sva_v_stack_ptr        = 0;
          past_sva_v_stack_ptr   = 0;
          sva_v_empty_chk_failed = 0;
          sva_v_full_chk_failed  = 0;
       end

`endif

       sva_std_edge_select #( severity_level, edge_expr)
         SVA_CHECKER_EDGE_SELECT( clk, sva_checker_clk);

// Example 3-46 Sampling of design variables for auxiliary state variables
       clocking sampling_ev @(posedge sva_checker_clk);
         input not_resetting, push, push_data, pop, pop_data;
       endclocking : sampling_ev

// Example 3-48 Coverage of stack fill levels
`ifndef SYNTHESIS
`ifdef COVER_ON
       (* category = category, checkerType = "RANGE", checkerLevel = 2, 
          checkerMin = 0, checkerMax = depth *)
       covergroup depth_cg @(sampling_ev);
         coverpoint sva_v_stack_ptr 
//           iff (sampling_ev.not_resetting && 
           iff (not_resetting && 
                |(past_sva_v_stack_ptr^sva_v_stack_ptr)) {
             bins observed_depth[] = {[0:depth]};}
         option.per_instance = 1;
         option.at_least = 1;
         option.name = "observed_outstanding_contents";
         option.comment = "Bin index is the observed fill level";
       endgroup : depth_cg
`endif
`endif

       always @(sampling_ev)
         sva_v_stack_ptr <= 
           (!sampling_ev.not_resetting) ? 
           0 :
           (sva_v_deferred_push && 
            sva_v_deferred_pop) ?
             sva_v_stack_ptr :
             (sva_v_deferred_push && 
             (sva_v_stack_ptr < depth)) ? 
               sva_v_stack_ptr + 1 : 
               (sva_v_deferred_pop &&
               (sva_v_stack_ptr > 0)) ? 
                 sva_v_stack_ptr - 1 :
                 sva_v_stack_ptr;

       generate 
         if( pop_lat > 1) begin : pop_lat_g_1
           reg   [pop_lat-1 : 0]  sva_v_deferred_pop_sr;
`ifndef SYNTHESIS
           initial sva_v_deferred_pop_sr  = 0;
`endif

           assign sva_v_deferred_pop = sva_v_deferred_pop_sr[pop_lat-1];
           always @(sampling_ev)
             sva_v_deferred_pop_sr <= 
               { sva_v_deferred_pop_sr[pop_lat-2 : 0],sampling_ev.pop}; 

         end : pop_lat_g_1
         if( pop_lat == 1) begin : pop_lat_e_1
             reg   sva_v_deferred_pop_sr;
`ifndef SYNTHESIS
             initial sva_v_deferred_pop_sr  = 0;
`endif

             assign sva_v_deferred_pop = sva_v_deferred_pop_sr;
             always @ (sampling_ev)
               sva_v_deferred_pop_sr <= sampling_ev.pop;

         end : pop_lat_e_1
         if( pop_lat == 0) begin : pop_lat_e_0
               assign sva_v_deferred_pop = sampling_ev.pop;
         end : pop_lat_e_0

`ifndef SYNTHESIS
         if (pop_lat < 0) begin : pop_lat_l_0
           initial sva_checker_error ("illegal pop_lat parameter value");
         end : pop_lat_l_0
`endif

         if( push_lat > 1) begin : push_lat_g_1
           reg   [push_lat-1 : 0]  sva_v_deferred_push_sr;
`ifndef SYNTHESIS
             initial sva_v_deferred_push_sr  = 0;
`endif

           assign sva_v_deferred_push = sva_v_deferred_push_sr[push_lat-1];
           always @(sampling_ev)
             sva_v_deferred_push_sr <= 
               { sva_v_deferred_push_sr[push_lat-2 : 0],sampling_ev.push}; 

         end : push_lat_g_1
         if( push_lat == 1) begin : push_lat_e_1
             reg   sva_v_deferred_push_sr;
`ifndef SYNTHESIS
             initial sva_v_deferred_push_sr  = 0;
`endif

             assign sva_v_deferred_push = sva_v_deferred_push_sr;
             always @ (sampling_ev)
               sva_v_deferred_push_sr <= sampling_ev.push;

         end : push_lat_e_1
         if( push_lat == 0) begin : push_lat_e_0
               assign sva_v_deferred_push = sampling_ev.push;
         end : push_lat_e_0

`ifndef SYNTHESIS
         if (push_lat < 0) begin : push_lat_l_0
               initial sva_checker_error ("illegal push_lat parameter value");
         end : push_lat_l_0
`endif

    `ifdef ASSERT_ON
         if( value_chk) begin : value_check
           reg [(elem_sz-1) : 0] sva_v_stack [0 : depth]; 
           wire [(elem_sz-1) : 0] sva_w_data;
           assign sva_w_data = sva_v_stack[sva_v_stack_ptr-1];

           always @(sampling_ev) 
             sva_v_stack[sva_v_stack_ptr] <= 
               !sampling_ev.not_resetting ?
               0 :
                (sva_v_deferred_push && sva_v_deferred_pop) ?
                  sva_v_stack[sva_v_stack_ptr] :
                  ((sva_v_stack_ptr < depth) &&
                  sva_v_deferred_push) ? 
                    sampling_ev.push_data :
                    sva_v_stack[sva_v_stack_ptr]; 


           // Event: our top is the same as the design's top of stack 
           // do not generate if <value_chk> = 0
// Example 3-9 Using category Attribute
           (* category = category *) assert_stack_value_chk : 
             assert property ( 
               @( posedge sva_checker_clk) 
                 disable iff( !not_resetting)
                   sva_v_deferred_pop |->
                     (!( !sva_v_deferred_push &&
                         !sva_v_full_chk_failed &&
                         (sva_v_stack_ptr > 0)) || 
                       (sva_w_data == pop_data)) &&
                     (( !sva_v_deferred_push &&
                       !sva_v_full_chk_failed &&
                       (sva_v_stack_ptr > 0) ) || 
                         ( (!sva_v_deferred_push) ||
                            (push_data == pop_data))))
                 else sva_checker_error("");
         end : value_check
     `endif

         if( hi_water_mark >0) begin : high_water_mark_check
    `ifdef ASSERT_ON

           (* category = category *) assert_stack_hi_water_chk :
             assert property( 
               @( posedge sva_checker_clk) 
                 disable iff( !not_resetting)
                   not( $rose(sva_v_stack_ptr > hi_water_mark))) 
             else sva_checker_error("");
    `endif
    `ifdef COVER_ON

// Example 3-51 Selecting a Coverage Point
           if( ( coverage_level_3&1 ) != 0) begin : cov_level_3_0
             (* category = category, checkerType = "LIMIT", checkerLevel = 3 *) 
// Example 6-1
               cover_stack_hi_water_chk :
                 cover property( 
                   @( posedge sva_checker_clk) 
                     not_resetting && 
                       $rose(sva_v_stack_ptr == hi_water_mark)); 
           end : cov_level_3_0
    `endif
         end : high_water_mark_check

    `ifdef ASSERT_ON
         if( push_pop_chk) begin : push_pop_check
           (* category = category *) assert_stack_push_pop_fail :
             assert property( 
               @( posedge sva_checker_clk) 
                 disable iff( !not_resetting)
                   not( not_resetting && 
                     sva_v_deferred_push && 
                     sva_v_deferred_pop))
              else sva_checker_error("");
         end : push_pop_check
    `endif
    `ifdef COVER_ON
         if( (coverage_level_1&1 ) != 0) begin : cov_level_1_0
           (* category = category, checkerType = "SEQ", checkerLevel = 1 *) 
             cover_number_of_pushes :
               cover property( 
                 @( posedge sva_checker_clk) 
                   ( not_resetting && push));
         end : cov_level_1_0
         if( (coverage_level_1&2 ) != 0) begin : cov_level_1_1
           (* category = category, checkerType = "SEQ", checkerLevel = 1 *) 
             cover_number_of_pops :
               cover property( 
                 @( posedge sva_checker_clk) 
                   ( not_resetting && pop));
         end : cov_level_1_1
         if( (coverage_level_1&4 ) != 0) begin : cov_level_1_2
           (* category = category, checkerType = "SEQ", checkerLevel = 1 *) 
             cover_push_followed_eventually_by_pop :
               cover property( 
                 @( posedge sva_checker_clk) 
                   ( not_resetting) throughout (
                     ( push && pop) or
                       ( push ##1 !push[*1:$] ##0 pop)));
         end : cov_level_1_2

`ifndef SYNTHESIS
         if( (coverage_level_2&1 ) != 0) begin : cov_level_2_0

           always @(sampling_ev) past_sva_v_stack_ptr<=sva_v_stack_ptr;

           depth_cg depth_cover = new();

         end : cov_level_2_0

`endif

         if( (coverage_level_3&2 ) != 0) begin : cov_level_3_1
           (* category = category, checkerType = "LIMIT", checkerLevel = 3 *) 
             cover_simultaneous_push_pop :
               cover property( 
                 @( posedge sva_checker_clk) 
                    ( not_resetting && push && pop));
         end : cov_level_3_1

         if( (coverage_level_3&4 ) != 0) begin : cov_level_3_2
           (* category = category, checkerType = "LIMIT", checkerLevel = 3 *) 
             cover_simultaneous_push_pop_when_empty :
               cover property( 
                 @( posedge sva_checker_clk) 
                   ( not_resetting && sva_v_deferred_push && 
                           sva_v_deferred_pop && 
                     sva_v_empty_chk_failed));
         end : cov_level_3_2

         if( (coverage_level_3&8 ) != 0) begin : cov_level_3_3
           (* category = category, checkerType = "LIMIT", checkerLevel = 3 *) 
             cover_simultaneous_push_pop_when_full :
               cover property( 
                 @( posedge sva_checker_clk) 
                   ( not_resetting && sva_v_deferred_push && 
                     sva_v_deferred_pop && sva_v_full_chk_failed));
         end : cov_level_3_3

// Example 3-47 Cover property in assert_stack for empty condition reached

         if( (coverage_level_3&16 ) != 0) begin : cov_level_3_4
           (* category = category, checkerType = "LIMIT", checkerLevel = 3 *) 
             cover_number_of_empty :
               cover property( 
                 @( posedge sva_checker_clk) 
                   ( not_resetting) throughout(
                     sva_v_deferred_pop ##1 
                       ( !$stable( sva_v_stack_ptr) && 
                         ( sva_v_stack_ptr ==0))));
         end : cov_level_3_4

         if( (coverage_level_3&32 ) != 0) begin : cov_level_3_5
           (* category = category, checkerType = "LIMIT", checkerLevel = 3 *) 
             cover_number_of_full :
               cover property( 
                 @( posedge sva_checker_clk) 
                   ( not_resetting) throughout(
                     sva_v_deferred_push ##1 
                       ( !$stable( sva_v_stack_ptr) && 
                         ( sva_v_stack_ptr == depth))));
         end : cov_level_3_5
    `endif

       endgenerate
/*
`ifndef SYNTHESIS
         initial if ( (coverage_level_2&1 ) != 0) begin : cov_level_2_0
             depth_cg depth_cover = new; 
           end : cov_level_2_0
`endif
*/
       always @( posedge sva_checker_clk) begin : flag_update
         // Flag to indicate empty poped  
         sva_v_empty_chk_failed <= 
           (!sampling_ev.not_resetting) ? 
             0 : 
             (sva_v_deferred_push && sva_v_deferred_pop) ?
               sva_v_empty_chk_failed :
               (sva_v_deferred_pop) ? 
                 (sva_v_stack_ptr == 0) :
                   (sva_v_deferred_push) ?
                   1'b0 :
                     sva_v_empty_chk_failed;

         sva_v_full_chk_failed <= 
           (!sampling_ev.not_resetting) ?
             0 :
             (sva_v_deferred_push && sva_v_deferred_pop) ?
               sva_v_full_chk_failed :
               (sva_v_deferred_push) ? 
                 (sva_v_stack_ptr >= depth) :
                   sva_v_full_chk_failed;
       end : flag_update

    `ifdef ASSERT_ON
       (* category = category *) assert_stack_overflow :
         assert property( 
           @( posedge sva_checker_clk) 
             disable iff( !not_resetting)
               not( $rose( sva_v_full_chk_failed)))
           else sva_checker_error("");
       (* category = category *) assert_stack_underflow :
         assert property( 
           @( posedge sva_checker_clk) 
             disable iff( !not_resetting)
               not( $rose( sva_v_empty_chk_failed)))
           else sva_checker_error("");

    `endif //  `ifdef ASSERT_ON
    `endif //  `ifdef SVA_ASSERT_AND_COVER

endinterface : assert_stack

