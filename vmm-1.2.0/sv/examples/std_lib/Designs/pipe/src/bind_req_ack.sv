/*===========================================================================

Copyright © 2004, 2005 Synopsys, Inc. All rights reserved. 

This SystemVerilog Assertion Example and the associated documentation
are confidential and proprietary to Synopsys, Inc. Your use or
disclosure of this SystemVerilog Assertion Checker is subject to the
terms and conditions of a written license agreement between you, or
your company, and Synopsys, Inc.

===========================================================================*/

bind pipe_tb.handshake_out assert_req_ack 
          #( 
             .severity_level(0),
             .options(0),
             .bw(10),
             .min_req_latency(0),
             .max_req_latency(10),
             .min_ack_latency(0),
             .max_ack_latency(10),
             .msg("output handshake checker error"),
             .category(0)
           )
     output_handshake_check
           ( 
            .clk(clk), 
            .reset_n(!reset), 
            .req(ready_out), 
            .ack(accepted_out), 
            .data_r({id_out, data_out})
           );
