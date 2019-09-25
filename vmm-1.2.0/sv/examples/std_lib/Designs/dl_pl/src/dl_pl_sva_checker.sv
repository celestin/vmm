/*===========================================================================

Copyright © 2004, 2005 Synopsys, Inc. All rights reserved. 

This SystemVerilog Assertion Example and the associated documentation
are confidential and proprietary to Synopsys, Inc. Your use or
disclosure of this SystemVerilog Assertion Checker is subject to the
terms and conditions of a written license agreement between you, or
your company, and Synopsys, Inc.

===========================================================================*/

// Example 3-59 Multi-Level Protocol Checker Architecture
// Two-level data link - physical layer checker	
// Packets of length 2 bytes only in this example

interface DL_PL_checker 
  #(parameter bit dl_pl_ack_assume = 0, dl_pl_req_assume = 0)
  (input rst, clk, req, ack, inout [7:0] data);

// physical layer checks

// properties of req
  property p_req1; // stable req
    @(posedge clk) disable iff (rst)
      $rose(req) |-> req[*1:$] ##0 ack;
  endproperty : p_req1

  property p_req2; // req Return-to-Zero
    @(posedge clk)  disable iff (rst)
      ack |-> ##1 !req;
  endproperty : p_req2

  property p_req3;
    @(posedge clk)  disable iff (rst)
      ack |-> ##[1:6] req;
  endproperty : p_req3

// properties of ack
  property p_ack1; // pulse only
    @(posedge clk) disable iff (rst)
      ack |-> ##1 !ack;
  endproperty : p_ack1

  property p_ack2; // no ack w/o req
    @(posedge clk) disable iff (rst)
      !req |-> !ack;
  endproperty : p_ack2

  property p_ack3; // ack latency
    @(posedge clk) disable iff (rst)
      $rose(req) |-> ##[1:5] ack;
  endproperty : p_ack3

  generate

    if (dl_pl_ack_assume) begin : drive_ack
      aa1: assert property (p_ack1);

      aa2: assert property (p_ack2);

      aa3: assert property (p_ack3);
    end : drive_ack

    else begin : verify_ack
      aa1: assert property (p_ack1) else 
        $display("ack too wide");

      aa2: assert property (p_ack2) else
        $display("spurious ack"); 

      aa3: assert property (p_ack3) else
        $display("ack too late");
    end : verify_ack

    if (dl_pl_req_assume) begin : drive_req
      ar1: assert property (p_req1);

      ar2: assert property (p_req2); 
 
      ar3: assert property (p_req3);  
    end : drive_req

    else begin : verify_req
      ar1: assert property (p_req1) else
        $display("req dropped");

      ar2: assert property (p_req2) else
        $display("req not returned to 0");  

      ar3: assert property (p_req3) else
        $display("req too late");  
    end : verify_req

  endgenerate
	
// link with DL layer

// variables for the DL layer
  logic [1:0][7:0] packet = 0;
  logic cnt = 0; // only 2 octets


  clocking p_clk  @(posedge clk);
    input rst, ack, data;
  endclocking : p_clk

// count 2 data octets 
  always @(p_clk)
    cnt <= rst ? 0 : p_clk.ack ? 
                       !cnt : cnt;  
  generate

    if (dl_pl_ack_assume) begin : drive_pl
// disassemble packet into octets
      assign data = rst ? 
        0 : ack ? 
        (cnt ? packet[1] : packet[0]) :
        0;

// assure stable packet during disassembly
      assume_data_2: assert property  
        ( disable iff (rst)
          (1'b1 ##1 !$fell(cnt)) 
            |-> $stable(packet)
         );
    end : drive_pl

    else begin : verify_dl
//assemble packet for DL layer assertions
      always @(p_clk)
        packet[cnt] <= p_clk.rst ?
           0 : p_clk.ack ? 
                 p_clk.data :
                  packet[cnt];
    end : verify_dl

  endgenerate

// data link layer check

  property p_data_1;
    @(posedge clk) 
    disable iff (rst)
      (1'b1 ##1 $fell(cnt)) 
         |-> ((^packet) == 0);
  endproperty : p_data_1

  generate

    if (dl_pl_ack_assume) begin : drive
// assumption on data
      adt1: assert property (p_data_1);
    end : drive

    else begin : verify
// assertion on data
      adt1: assert property (p_data_1) else 
                  $display("data_property failed");
    end : verify    

  endgenerate

endinterface : DL_PL_checker