/*===========================================================================

Copyright © 2004, 2005 Synopsys, Inc. All rights reserved. 

This SystemVerilog Assertion Example and the associated documentation
are confidential and proprietary to Synopsys, Inc. Your use or
disclosure of this SystemVerilog Assertion Checker is subject to the
terms and conditions of a written license agreement between you, or
your company, and Synopsys, Inc.

===========================================================================*/


// Testbench for illustrating the use of the assert_stack checker
module test;

   parameter elem_sz = 4;
   parameter depth = 6;
   parameter push_lat = 2;
   parameter pop_lat = 2;
   parameter hi_water_mark = 3;
   parameter pop_nos = 4; // the number of pops parameterised
   parameter push_nos = 4; // the number of pushs parameterised
 
   integer i;

   reg push;
   reg pop;
   reg clk;
   reg reset;
   reg [elem_sz-1 : 0]   push_data;
   wire [elem_sz-1 : 0]   pop_data;

   stack my_stack( clk, reset, push, pop, push_data, pop_data);

   initial 
   begin
      $vcdpluson;
      clk = 0;
      push = 0;
      pop = 0;
      reset = 1;
      push_data = 0;
      repeat(2) @ ( posedge clk);
      reset <= 0;
      @ ( posedge clk);
      for( i = 0; i< push_nos; i=i+1) begin
        fork
          begin
            push <= 1;
            @ ( posedge clk);
            push <= 0;
            @ ( posedge clk);
          end
          begin
            repeat( push_lat) @ ( posedge clk);
            push_data <= i[elem_sz-1:0];
            @ ( posedge clk);
          end
        join
      end

      for( i = 0; i< pop_nos; i=i+1) begin
        pop <= 1;
        @ ( posedge clk);
        pop <= 0;
        repeat( pop_lat) @ ( posedge clk);
      end

      repeat (5) @ ( posedge clk);
      $finish;
   end

   always #2 clk = ~clk;

assert_stack #(.depth(6),.elem_sz(4),.hi_water_mark(3),
               .push_lat(2),.pop_lat(2),.value_chk(1),
               .push_pop_chk(1),.edge_expr(0),.msg("stack_triggered"), 
               .coverage_level_1(7), .coverage_level_2(1), .coverage_level_3('hff))
        assert_stack_inst (.reset_n(!reset),.clk(clk),
                           .push(push),.push_data(push_data),
                           .pop(pop),.pop_data(pop_data));

endmodule : test

module stack( clk, reset, push, pop, push_data, pop_data);

   parameter elem_sz = 4;
   parameter depth = 6;
   parameter push_lat = 2;
   parameter pop_lat = 2;
   parameter hi_water_mark = 3;

   input                 clk;
   input                 reset;
   input                 push;
   input                 pop;

   input [elem_sz-1 : 0] push_data;
   output [elem_sz-1 : 0] pop_data;


   reg [elem_sz-1 : 0]   pop_data = 0;
   reg [elem_sz-1 : 0]   pop_data_w;
   reg [elem_sz-1 : 0]   stack[0: depth-1];

   integer               stack_ptr;
   
   always @ ( negedge clk) begin
     if( reset ) stack_ptr = 0;
   end
   
   always @ ( negedge clk)  begin : push_pop
     if( push && !pop) begin
       if( stack_ptr == hi_water_mark+1) 
           $display("High_water_mark will flag failure now");
       if( stack_ptr < depth)  begin
         repeat( push_lat)  @ ( negedge clk);
         stack[stack_ptr] <=  push_data;
         $display("%x pushed on stack location %d at time %d ", 
                    push_data, stack_ptr, $time);
         stack_ptr <= stack_ptr + 1;
       end
       else begin
         $display("Overflow happened");
       end 
     end
     if( pop && !push) begin
       if ( stack_ptr > 0)  begin
         repeat( pop_lat) @ ( negedge clk);
         pop_data_w = {$random}%2 ? stack[stack_ptr-1] : $random;
         pop_data <= pop_data_w;
         stack_ptr <= stack_ptr - 1;  
         $display("%x popped off stack location %d at time %d ", 
                   pop_data_w, stack_ptr-1, $time);
       end
       else begin
         $display("Underflow happened");
       end
     end

   end : push_pop

endmodule : stack
