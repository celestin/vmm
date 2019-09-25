/*===========================================================================

Copyright © 2004, 2005 Synopsys, Inc. All rights reserved. 

This SystemVerilog Assertion Example and the associated documentation
are confidential and proprietary to Synopsys, Inc. Your use or
disclosure of this SystemVerilog Assertion Checker is subject to the
terms and conditions of a written license agreement between you, or
your company, and Synopsys, Inc.

===========================================================================*/

// Example of a simple pipeline

// random testbench for a pipelined operation example.
`timescale 1 ns / 1 ns

interface itf_in(input clk, reset);
  wire [7:0]  data_in;
  reg  [1:0]  id_in;
  wire        ready_in;
  wire        accepted_in;
// Example 3-6 Assertions in an interface declaration
// Example 3-32 Checking assertion
`ifndef NO_INLINED_ASSERTION
// Example 3-52 Assertion implementing a protocol rule
  a0: assert property (
    @(posedge clk) disable iff (reset) 
      (!ready_in || accepted_in) ##1 ready_in 
        |-> ##[1:10] accepted_in ) 
        else $display("accepted_in not arrived with 5 to 10 clock cycles");

  a1: assert property (
    @(posedge clk) disable iff (reset) 
      $rose(ready_in) || (ready_in && $past(accepted_in))
        |-> ready_in[*1:$] ##0 accepted_in ) 
        else $display("ready_in not asserted till accepted_in");

// Example 3-53 Assertion implementing a protocol rule
// Example 7-4 Avoiding initial unknown value
  a1_good: assert property (
    @(posedge clk) disable iff (reset) 
     (!ready_in || accepted_in) ##1 ready_in
        |-> ready_in[*1:$] ##0 accepted_in ) 
        else $display("A1_good: ready_in not asserted till accepted_in");


  a2: assert property (
    @(posedge clk) disable iff (reset) 
      accepted_in |-> ##1 !accepted_in ) 
        else $display("accepted_in wider than one clock cycle");

  a3: assert property (
    @(posedge clk) disable iff (reset) 
      (!ready_in || accepted_in) ##1 ready_in
        |-> 
           accepted_in or (##1 ($stable(data_in)[*1:$]) ##0 accepted_in ) ) 
        else $display("data_in not stable till accepted_in");
`endif

// Example 3-33 Cover property
// Example 3-34 Using throughout to disable cover property
// Example 3-49 Delay coverage using cover property
`ifndef NO_INLINED_ASSERTION
c1: cover property (
  @(posedge clk) (!reset) throughout
       (!ready_in || accepted_in) ##1
       ready_in ##[1:$] accepted_in );  
`endif

endinterface : itf_in

interface itf_out(input clk, reset);
  wire [7:0]  data_out;
  wire [1:0]  id_out;
  wire        ready_out;
  wire        accepted_out;
endinterface : itf_out

module pipe_tb();
  parameter MAX_TIME   = 1000;

  // state values
  localparam IDLE       = 1'b0;
  localparam DATA_READY = 1'b1;

  reg         clk;
  reg         reset;
  reg [7:0]   data_in_ND;
  reg         ready_in_ND;
  reg         accepted_out_ND;
  reg         state_in, state_out;
  reg  [7:0]  pre_data_in;


  // compute next state for handshake protocol
  function next_st(input state, ready, accepted);
    next_st = (ready && state==IDLE) ? 
                 DATA_READY :
                 ((accepted && state==DATA_READY) ? 
                    IDLE : state );
  endfunction // next_st

  itf_in handshake_in(clk, reset);
  itf_out handshake_out(clk, reset);

  initial begin
    $vcdpluson;
    reset = 1;
    clk = 0;
    #21 reset = 0;
    #MAX_TIME $finish;
  end

  always #10 clk = ~clk;

// Example 3-31 Labeling of blocks
  always @(posedge clk) begin : select_random
    if (reset) begin : resetting
      ready_in_ND <= 0;
      accepted_out_ND <= 0;
      data_in_ND <= 0;
    end : resetting
    else begin : normal
      ready_in_ND <= (({$random} % 10) > 4);
      accepted_out_ND <= (({$random} % 10) > 3);
      data_in_ND <= {$random} % 256;
    end : normal
  end : select_random

  always @(posedge clk) begin : drive_protocols
    if (reset) begin
      state_in <= IDLE;
      state_out <= IDLE;
      pre_data_in <= 0;
      handshake_in.id_in <= 0;
    end
    else begin
      state_in <= next_st(state_in, ready_in_ND, handshake_in.accepted_in);
      state_out <= next_st(state_out, handshake_out.ready_out, 
                                      handshake_out.accepted_out);
      pre_data_in <= handshake_in.data_in;
      handshake_in.id_in <= handshake_in.accepted_in ? 
                              handshake_in.id_in + 2'b01 :
                              handshake_in.id_in;
    end 
  end : drive_protocols

  assign handshake_in.ready_in = ((state_in == IDLE) && ready_in_ND) ||
                    (state_in == DATA_READY);
  assign handshake_in.data_in = (state_in == IDLE) ? data_in_ND : pre_data_in;
   
  assign handshake_out.accepted_out = (state_out == DATA_READY) && accepted_out_ND;



  // pipelined operation DUT instance
  operation_pipe oper_pipe_inst(clk, reset, 
                                handshake_in,
                                handshake_out);
/*
  // output interface checker instance
  assert_req_ack 
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
            .req(handshake_out.ready_out), 
            .ack(handshake_out.accepted_out), 
            .data_r({handshake_out.id_out, handshake_out.data_out})
           );
*/
endmodule : pipe_tb

/* 
 
The DUT is an pipelined operation described as a functional yet
synthesizable model. It has two interfaces : in and out, both obeying
the same simple NRZ handshake protocol.
 
Protocol: 

On in I/F when data is ready by the environment, it places data on
data_in and asserts ready_in. When operation accepts data, it raises
accepted_in for one cycle.
 
On the output I/F, when data_out is produced by operation, it puts it
on data_out and raises ready_out until the environment accepts the
data by raising accepted_out for one cycle.

The time to process the data is 4 cycles, i.e., 4 cycles after
accepted_in is asserted, ready_out should be asserted.
 
This design is pipelined, so that it can accept new data while there
is room in the pipe. However, when accepted_out is delayed the pipe
stalls even though there are stages that could continue operating,
i.e., the pipe is not "flexible".

Upon reset, ready_in == 0, ready_out == 0, accepted_in == 0,
accepted_out == 0.

*/

module operation_pipe(input clk, reset, 
                      itf_in port_in,
                      itf_out port_out);

  // control and status between the control and the datapath
  wire         all_empty;
  wire         stall;
  wire         valid_in;

  genvar       i, j, k;

  oper_cntrl_pipe cntrlr_pipe( 
             clk, reset,
             all_empty, port_out.ready_out, port_in.ready_in,  
             port_out.accepted_out, port_in.accepted_in,
             valid_in, stall);
        
  oper_datapath_pipe oper_pipe_inst(
             clk, reset, port_in.data_in, port_in.id_in, valid_in, stall, 
             all_empty, port_out.data_out, port_out.id_out, port_out.ready_out);

// Example 7-11 Data in -> Data out, using local variable
`ifndef NO_INLINED_ASSERTION
  property data_check_p;
    logic [7:0] v_data_in;
    @(posedge clk) disable iff (reset) 
    (all_empty && port_in.accepted_in, v_data_in=port_in.data_in)
       |-> 
         ##4 (port_out.data_out == (v_data_in << 1));
  endproperty : data_check_p
  data_check: assert property (data_check_p)
    else $display ("Incorrect data out");
`endif

// Example 7-12 Data in -> Data out, using enumeration
// Not to be used with a large range of data.
// In this case use of $past(port_in.data_in, 4) is better
`ifndef NO_INLINED_ASSERTION
  generate
    for (i=0; i<=255; i=i+1) begin : forall_7_12
      property p;
        @(posedge clk) disable iff (reset) 
        (all_empty && port_in.accepted_in && (i==port_in.data_in))
          |-> 
            ##4 (port_out.data_out == (i << 1));
      endproperty : p
      data_check: assert property (p)
        else $display ("Incorrect data out");
    end : forall_7_12
  endgenerate
`endif

// Example 3-26 Checking expected value in non-overlapping transaction
// Example 3-30 Using an always block to infer a clock
`ifndef NO_INLINED_ASSERTION
  logic [7:0] v_data_in = 0;
  always @(posedge clk) begin : no_overlap
    v_data_in <= port_in.accepted_in && all_empty ? 
                            port_in.data_in : v_data_in;
    data_check: assert property (
       disable iff (reset) 
       all_empty && port_in.accepted_in |-> 
            ##4 (port_out.data_out == (v_data_in << 1)) )
      else $display ("Incorrect data out in non-overlapping case");
  end : no_overlap
`endif


// Example 3-27 Checking expected value in overlapping transactions
// Example 7-13 Checking tagged data with local variables
`ifndef NO_INLINED_ASSERTION
  property p;
    logic [7:0] v_data_in;
    logic [1:0] v_id_in;
    @(posedge clk) disable iff (reset)
      (port_in.accepted_in, v_data_in = port_in.data_in, 
                            v_id_in = port_in.id_in) ##1 
      (port_out.accepted_out && (port_out.id_out==v_id_in))[->1]  
        |-> 
          (port_out.data_out ==  (v_data_in + v_data_in));
  endproperty : p
  overlap_data_check: assert property(p) 
    else $display("Incorrect data out in overlapping transactions");
`endif

// Example 7-14 Checking tagged data using enumeration and an array for data
// Should also check that while an input with a certain id is being 
// processed no new transaction is issued with the same id
`ifndef NO_INLINED_ASSERTION
  generate
    for (i=0; i<4; i=i+1) begin : forall_id_7_14
      logic [7:0] v_data_in;
      always @(posedge clk) begin : each_id
        v_data_in <=
          reset ? 0 :
            port_in.accepted_in && (port_in.id_in == i) ? port_in.data_in :
              v_data_in;
        data_check: assert property (
          disable iff (reset)
          port_out.accepted_out && (port_out.id_out==i)
            |->
              (port_out.data_out == (v_data_in<<1)) ) 
          else $display("Incorrect data out in overlapping transactions");
        id_check: assert property (
          port_in.accepted_in && (port_in.id_in == i)
            |=>
               !(port_in.accepted_in && (port_in.id_in == i))
                   throughout
                   (port_out.accepted_out && (port_out.id_out==i))[->1] )
          else $display("Id %d issued while being processed", i);
      end : each_id
    end : forall_id_7_14
  endgenerate
`endif

// Example 7-15 Checking tagged data using enumeration over tag and 
// bit position enumeration 
// There will be 4x256 == 1024 assertions
`ifndef NO_INLINED_ASSERTION
  logic [7:0] sum_data; // result predictor
  always @(port_in.data_in) sum_data = (port_in.data_in<<1);
  generate
    for (i=0; i<4; i=i+1) begin : forall_id_7_15
      for (j=0; j<256; j=j+1) begin : forall_data_7_15
        overlapped_data_check: assert property(
          @(posedge clk) disable iff (reset)
          port_in.accepted_in && 
          (sum_data == j) && 
          (port_in.id_in == i) ##1 
            (port_out.accepted_out && (port_out.id_out==i))[->1]  
              |->
                (port_out.data_out == j) )
           else $display("Incorrect data out in overlapping transactions");
      end : forall_data_7_15
    end : forall_id_7_15
  endgenerate
`endif

// Example 7-16  Checking tagged data using enumeration over tag and 
// bit index enumeration with bit value enumeration over data
// There will be 4x8x2 = 64 assertions compared to 1024 if full 
// enumeration over data and id were used
`ifndef NO_INLINED_ASSERTION
  generate
    for (i=0; i<4; i=i+1) begin : forall_id_7_16
      for (j=0; j<8; j=j+1) begin : forall_index_7_16
        for (k=0; k<2; k=k+1) begin : forall_bit_7_16
          overlapped_data_check: assert property(
            @(posedge clk) disable iff (reset)
            port_in.accepted_in && 
            (sum_data[j] == k) && 
            (port_in.id_in == i) ##1 
            (port_out.accepted_out && (port_out.id_out==i))[->1]  
              |->
                (port_out.data_out[j] == k) )
           else $display("Incorrect data out in overlapping transactions");
        end : forall_bit_7_16
      end : forall_index_7_16
    end : forall_id_7_16
  endgenerate
`endif


// Checking tag liveness using enumeration tag bits and bit values
// In this case, due to the small range of the id's, enumeration over its values or 
// over the bit positions and their values is of the same cost, but
// for larger ranges this approach is more efficient.
`ifndef NO_INLINED_ASSERTION
  generate
    for (i=0; i<2; i=i+1) begin : forall_id_bits
      for (j=0; j<2; j=j+1) begin : forall_bit_value
        pipe_liveness: assert property(
            @(posedge clk) disable iff (reset)
            port_in.accepted_in && 
            (port_in.id_in[i] == j) 
              |-> 
                ##[1:10] (port_out.ready_out && (port_out.id_out[i]==j)) ) 
         else $display("Transaction not output in 1 to 10 clock cycles");
      end : forall_bit_value
    end : forall_id_bits
  endgenerate
`endif

endmodule : operation_pipe

/*

Controller for a pipelined operation.

Stalls when waiting for acknowledgment of its output,
i.e., when ready_out is asserted, but not yet accepted_out 
asserted by the environment.

st_in indicates that it is waiting for the pipe to be freed 
to accept next data.

*/

module oper_cntrl_pipe (clk, reset, all_empty, ready_out, 
                        ready_in, accepted_out, accepted_in, 
                        valid_in, stall);
  input     clk, reset; 
  input     all_empty; 
  input     ready_out; 
  input     ready_in;  
  input     accepted_out; 
  output    accepted_in; 
  output    valid_in;
  output    stall;

  reg        st_in;

  wire   accepted_in, valid_in, stall;

  assign stall = ready_out && !accepted_out;
  assign valid_in = accepted_in;
  assign accepted_in = st_in && !stall;

// Example 3-2 Clock and condition extraction from always block
// Example 3-4 Controlling the introduction of inlined assertions
// using NO_INLINED_ASSERTION macro
  always @(posedge clk)
    if (reset) st_in <= 0;
    else
      if (!st_in && ready_in) begin : set_st_in
        st_in <= 1; 
`ifndef NO_INLINED_ASSERTION
        st_hold: assert property(##1 (st_in [*1:$]) ##0 accepted_in) 
                else $display("st_in did not hold until accepted_in");
`endif
      end
      else if (st_in && accepted_in) st_in <= 0;

// Example 3-3 Equivalent assertion to Example 3-2
`ifndef NO_INLINED_ASSERTION
        st_hold: assert property( @(posedge clk)
                (!reset && (!st_in && ready_in)) 
                   |->
                      ##1 (st_in [*1:$]) ##0 accepted_in) 
                else $display("st_in did not hold until accepted_in");
`endif
   
endmodule : oper_cntrl_pipe

/*

Four-stage pipelined operation datapath.
The operation is a simple doubling of the 8-bit operand.
The pipeline is described functionally, using a delay line and
the operation performed combinationally.

The actual operation could be anything, and additional
status flags can be added.
 
*/

module oper_datapath_pipe (clk, reset, data_in, id_in, valid_in, stall, 
                           all_empty, data_out, id_out, ready_out);
  input        clk;
  input        reset; 
  input [7:0]  data_in; 
  input [1:0]  id_in;
  input        valid_in;
  input        stall;  
  output [7:0] data_out; 
  output [1:0] id_out;
  output       ready_out;
  output       all_empty;

  wire   [7:0] data_out;
  wire         ready_out;
  wire         all_empty;

  wire [7:0]   d0; // input (computes the combinational function)
  reg  [7:0]   r0, r1, r2, r3; // 4 stage registers
  reg  [1:0]   id0, id1, id2, id3;
  reg          f0, f1, f2, f3; // stage occupied flags

  assign     all_empty = !(f0 || f1 || f2 || f3);
  assign     data_out = (reset || !ready_out) ? 'bz : r3;
  assign     id_out = (reset || !ready_out) ? 'bz : id3;
  assign     ready_out = f3;
  assign     d0 = data_in + data_in;

// Example 3-7 Trivial assertion
`ifndef NO_INLINED_ASSERTION
  useless_assert : assert property( 
    @(posedge clk) disable iff (reset)
          d0 == data_in + data_in );

// Example 3-8 Using reset to verify signal values
// Example 3-42 Use of SYNTHESIS macro
// Example 3-10 Using VMM log class for reporting
`ifndef SYNTHESIS
//  vmm_log log = new("pipeline checks", $psprintf(%m)); //***VMM***

  check_z : assert property( @(negedge reset) data_out === 8'bzzzzzzzz )
//      else `vmm_error(log, "data_out not Hi-Z when in reset") //***VMM***
       ;
`endif
`endif  
  always @(posedge clk) begin : data_pipe

    if (reset) begin : resetting
      f0 <= 0;
      f1 <= 0;
      f2 <= 0;
      f3 <= 0;
      id0 <= 0;
      id1 <= 0;
      id2 <= 0;
      id3 <= 0;
    end : resetting
    else
      if (!stall)  begin : no_stall
        r3 <= r2;
        r2 <= r1;
        r1 <= r0;
        r0 <= d0;
        id3 <= id2;
        id2 <= id1;
        id1 <= id0;
        id0 <= id_in;
        f3 <= f2;
        f2 <= f1;
        f1 <= f0;
        f0 <= valid_in;
      end : no_stall

  end : data_pipe

// Example 3-1 Inlined assertion
// Example 3-5 Reset in disable iff
// Example 3-28 Using disable iff on reset
`ifndef NO_INLINED_ASSERTION
  check_progress : assert property (
     @(posedge clk) disable iff (reset)
        (valid_in && !stall) ##1 (!stall[->3]) |-> ##1 f3 )
//     else `vmm_error(log, "Pipe not progressing correctly") //***VMM***
     ;
`endif

endmodule : oper_datapath_pipe

