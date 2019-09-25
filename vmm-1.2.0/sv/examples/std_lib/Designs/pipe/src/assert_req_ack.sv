/*===========================================================================

Copyright © 2004, 2005 Synopsys, Inc. All rights reserved. 

This SystemVerilog Assertion Example and the associated documentation
are confidential and proprietary to Synopsys, Inc. Your use or
disclosure of this SystemVerilog Assertion Checker is subject to the
terms and conditions of a written license agreement between you, or
your company, and Synopsys, Inc.

===========================================================================*/

interface assert_req_ack
  #( parameter 
               severity_level       = 0,
               options              = 0,
               bw                   = 8,
               min_req_latency      = 0,
               max_req_latency      = 0,
               min_ack_latency      = 0,
               max_ack_latency      = 0,
               msg                  = "VIOLATION",
               category             = 0
   )
   ( 
     input          clk, reset_n, req, ack, 
     input [bw-1:0] data_r
   );

`ifndef SYNTHESIS

     localparam     assert_name = "ASSERT_REQ_ACK";
`endif

    `include "sva_std_task.h"


// Example 7-10 Auxiliary state machine

  enum {IDLE, W_ACK, RZ} state;

  clocking ck @(posedge clk);
    input req, ack; // #1step req, ack;
  endclocking : ck

  always @(ck) begin : req_ack
    if (reset_n)
      case (state)
        IDLE:      if (ck.req && !ck.ack) state <= W_ACK;
        W_ACK:  if (ck.ack)         state <= RZ;
        RZ:        state <= IDLE;
      endcase
    else state <= IDLE;
  end : req_ack

  always @(posedge clk) begin : req_ack_assert
    // Slave (ack) safety check
    S1: assert property( disable iff (!reset_n)
          !req |-> !ack ) else sva_checker_error("");
    // Master (req) safety check
    M1: assert property( disable iff (!reset_n)
          (state == W_ACK) |-> req ) else sva_checker_error("");
   // Master return to 0
    M2: assert property( disable iff (!reset_n)
          (state == RZ) |-> !req ) else sva_checker_error("");
  end : req_ack_assert

// Example 7-4 Avoiding Initial Unknown Value
// Master liveness (on req)
  generate
    if ((max_req_latency == 0) && (min_req_latency > 0)) begin : req_lower_bound
      M3 : assert property (
        @(posedge clk) disable iff (!reset_n) 
           !(state == IDLE) ##1 (state == IDLE) && !req 
                    |-> (!req)[*min_req_latency] ) 
        else sva_checker_error("");
    end : req_lower_bound
    else if ((max_req_latency >= 0) && 
             (max_req_latency >= min_req_latency)) begin : req_bounded
      M3 : assert property (
        @(posedge clk) disable iff (!reset_n) 
           !(state == IDLE) ##1 (state == IDLE) 
                    |-> ##[min_req_latency:max_req_latency] req ) 
        else sva_checker_error("");
    end : req_bounded
    else begin : req_no_liveness
    `ifndef SYNTHESIS
      initial sva_checker_warning_msg("No req liveness constraint");
    `endif
    end : req_no_liveness
  endgenerate

// Slave liveness (on ack)
  generate
    if ((max_ack_latency == 0) && (min_ack_latency > 0)) begin : ack_lower_bound
      S2: assert property(
        @(posedge clk) disable iff (!reset_n) 
           (state == IDLE) && req 
                    |-> (!ack)[*min_ack_latency] )
        else sva_checker_error("");
    end : ack_lower_bound
    else if ((max_ack_latency >= 0) && 
             (max_ack_latency >= min_ack_latency)) begin : ack_bounded
      S2: assert property(
        @(posedge clk) disable iff (!reset_n) 
           (state == IDLE) && req |-> 
                            ##[min_ack_latency:max_ack_latency] ack)
        else sva_checker_error("");
    end : ack_bounded
    else begin : ack_no_liveness
    `ifndef SYNTHESIS
      initial sva_checker_warning_msg("No ack liveness constraint");
    `endif
    end : ack_no_liveness
  endgenerate

endinterface : assert_req_ack
