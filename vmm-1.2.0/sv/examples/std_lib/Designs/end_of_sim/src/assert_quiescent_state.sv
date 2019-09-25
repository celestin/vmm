/*===========================================================================

Copyright © 2004, 2005 Synopsys, Inc. All rights reserved. 

This SystemVerilog Assertion Example and the associated documentation
are confidential and proprietary to Synopsys, Inc. Your use or
disclosure of this SystemVerilog Assertion Checker is subject to the
terms and conditions of a written license agreement between you, or
your company, and Synopsys, Inc.

===========================================================================*/

/*

assert_quiescent_state

The assert_quiescent_state checker verifies that the value in the
variable, state_expr, is equal to the value specified by check_value
and optionally at the end of simulation. Verification occurs when a
sampled positive edge is detected on sample_event.

SYNTAX  

assert_quiescent_state [#(severity_level, width, options, msg, category,
                 coverage_level_1, coverage_level_2, coverage_level_3)] 
            inst_name (clk, reset_n, state_expr, check_value, sample_event);

ARGUMENTS
 
severity_level : Severity of the failure with default value 
                 of 0. 

width          : Width of the monitored expression state_expr.

options        : Currently, the only supported 
                 option is options=1, which defines the assertion 
                 as a constraint on formal tools. 
                 The default value is options=0, or no options 
                 specified. 

msg            : Error message will be printed if the assertion 
                 fires. 

inst_name      : Instance name of assertion monitor. 

clk            : Sampling clock of the checker. 

reset_n        : Signal indicating completed initialization 
                 (for example, a local copy of reset_n of a global 
                  reference to reset_n). 

state_expr     : Expression being verified at the positive edge of clk.

check_value    : Specified value for state_expr when quiescent. (I.e.,  
                 a signal that holds the value to be compared with state_expr 
                 when sample_event is asserted.)

sample_event   : Sampled rasising transition triggers the quiescent state check.

`ASSERT_END_OF_SIMULATION : This macro can be used to quiescent the state
                            expression at the end of simulation. 
                            For example,
                            +define+ASSERT_END_OF_SIMULATION=top.sim_end
Coverage modes :

cov_level_1_0 (bit 0 set in coverage_level_1) :

  Cover property cover_quiescent_state indicates that the 
  quiescent state was reached
 
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

(* sva_checker *)
interface assert_quiescent_state(clk, reset_n, state_expr, check_value, 
                                 sample_event);

       parameter              severity_level       = 0;
       parameter              width                = 1;
       parameter              options              = 0;
       parameter              msg                  = "VIOLATION";
       parameter              category             = 0;
       parameter              coverage_level_1     = 15;
       parameter              coverage_level_2     = 0;
       parameter              coverage_level_3     = 0;
       input                  clk;
       input                  reset_n;
       input [(width - 1):0]  state_expr;
       input [(width - 1):0]  check_value;
       input                  sample_event;

     `ifdef SVA_ASSERT_AND_COVER

       localparam             assert_name          = "ASSERT_QUIESCENT_STATE";

       wire                   clk;
       wire                   reset_n;
       wire  [(width - 1):0]  state_expr;
       wire  [(width - 1):0]  check_value;
       wire                   sample_event;

     `include "sva_std_task.h"

     `ifdef COVER_ON
       generate  
         if( ( coverage_level_1&1) != 0 ) begin : cov_level_1_0
     `ifdef ASSERT_END_OF_SIMULATION   
           (* category = category, checkerType = "SEQ", checkerLevel = 1 *) 
             cover_quiescent_state :
               cover property( 
                 @(posedge clk) 
                   ( ( not_resetting && $rose(sample_event)) ||
                       $rose(`ASSERT_END_OF_SIMULATION ==1'b1) ) && 
                       ( state_expr == check_value) ) ;
     `else 
           (* category = category, checkerType = "SEQ", checkerLevel = 1 *) 
             cover_quiescent_state :
               cover property( 
                 @( posedge clk) 
                   ( not_resetting && $rose(sample_event))  &&
                      ( state_expr == check_value) );
     `endif
         end : cov_level_1_0
       endgenerate
     `endif // COVER_ON
 
     `ifdef ASSERT_ON

// Example 3-50 Triggering by ASSERT_END_OF_SIMULATION
     `ifdef ASSERT_END_OF_SIMULATION   
      (* category = category *) assert_quiescent_state: 
        assert property(
          @( posedge clk) 
            disable iff( !not_resetting)
             ( !sample_event ##1 sample_event) or
               $rose(`ASSERT_END_OF_SIMULATION ==1'b1) |-> 
                             ( state_expr == check_value) )
          else sva_checker_error("");
     `else 
      (* category = category *) assert_quiescent_state: 
        assert property(
          @( posedge clk) 
            disable iff( !not_resetting)
           ( !sample_event ##1 sample_event) |-> 
             ( state_expr == check_value) )
          else sva_checker_error("");
     `endif
     `endif // ASSERT_ON
     `endif // SVA_ASSERT_AND_COVER 

endinterface

